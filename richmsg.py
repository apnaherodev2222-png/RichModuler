"""richmsg — Portable Telegram Rich Message client.

Zero project dependencies. Only stdlib + requests.

Quick start:
    from richmsg import RichClient, heading, paragraph, success_card

    client = RichClient(token="YOUR_BOT_TOKEN")

    async def my_handler(update, context):
        async def fallback():
            return await update.message.reply_text("Done")

        await client.send_or(
            chat_id=update.effective_chat.id,
            blocks=success_card("Done", "Kaam ho gaya"),
            fallback=fallback,
        )
"""

from __future__ import annotations

import asyncio
import logging
import time
from typing import Any, Callable, Dict, List, Optional, Sequence
from weakref import WeakValueDictionary

import requests

logger = logging.getLogger("richmsg")


class RichMessageError(Exception):
    """Raised when Telegram rejects or cannot receive a rich-message call."""

    def __init__(self, message: str, *, retry_after: Optional[float] = None) -> None:
        super().__init__(message)
        self.retry_after = retry_after


class RichMessageValidationError(RichMessageError):
    """Raised when blocks fail validation — caller's fault, not transport."""


_VALID_BLOCK_TYPES = frozenset({
    "heading", "paragraph", "table", "video", "photo", "buttons",
    "divider", "spacer", "quote", "code", "list", "checklist",
    "details", "spoiler", "markdown", "animation", "audio", "document",
})

_TRANSIENT_MARKERS = (
    "connection reset", "connection aborted", "temporarily unavailable",
    "timed out", "timeout", "bad gateway", "gateway timeout",
    "service unavailable", "too many requests", "http 5", "http 429",
)

_STRIPPABLE_BLOCK_TYPES = frozenset(("video", "photo", "animation", "audio"))


def heading(text: str, size: int = 2) -> Dict[str, Any]:
    """Build a heading block."""
    return {"type": "heading", "text": str(text), "size": int(size)}


def paragraph(text: str) -> Dict[str, Any]:
    """Build a paragraph block."""
    return {"type": "paragraph", "text": str(text)}


def video(url: str) -> Dict[str, Any]:
    """Build a video block."""
    return {"type": "video", "video": {"type": "video", "media": str(url)}}


def compact_table(
    header_row: Sequence[str], data_rows: Sequence[Sequence[str]]
) -> Dict[str, Any]:
    """Build the compact table shape used by the source project."""
    def cell(text: Any, is_header: bool = False) -> Dict[str, Any]:
        item: Dict[str, Any] = {"text": str(text), "align": "left", "valign": "middle"}
        if is_header:
            item["is_header"] = True
        return item

    cells: List[List[Dict[str, Any]]] = [[cell(value, True) for value in header_row]]
    cells.extend([[cell(value) for value in row] for row in data_rows])
    return {"type": "table", "is_compact": True, "cells": cells}


def button_row(buttons: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
    """Build one in-message button row."""
    out: List[Dict[str, Any]] = []
    for button in buttons:
        item: Dict[str, Any] = {"text": str(button["text"])}
        if button.get("callback_data") is not None:
            item["callback_data"] = str(button["callback_data"])
        elif button.get("url") is not None:
            item["url"] = str(button["url"])
        if button.get("style") is not None:
            item["style"] = str(button["style"])
        out.append(item)
    return {"type": "buttons", "buttons": out}


def divider() -> Dict[str, Any]:
    """Build a full-width divider block."""
    return {"type": "divider"}


def spacer(height: int = 8) -> Dict[str, Any]:
    """Build a vertical spacer block."""
    return {"type": "spacer", "height": int(height)}


def quote(text: str, author: Optional[str] = None) -> Dict[str, Any]:
    """Build a quote block."""
    block: Dict[str, Any] = {"type": "quote", "text": str(text)}
    if author:
        block["author"] = str(author)
    return block


def code(text: str, language: Optional[str] = None) -> Dict[str, Any]:
    """Build a code block."""
    block: Dict[str, Any] = {"type": "code", "text": str(text)}
    if language:
        block["language"] = str(language)
    return block


def markdown(text: str) -> Dict[str, Any]:
    """Build a markdown block."""
    return {"type": "markdown", "text": str(text)}


def bullet_list(items: Sequence[str]) -> Dict[str, Any]:
    """Build a list block."""
    return {"type": "list", "items": [str(item) for item in items]}


def checklist(items: Sequence[Sequence[Any]]) -> Dict[str, Any]:
    """Build a checklist from (text, checked) pairs."""
    return {
        "type": "checklist",
        "items": [{"text": str(item[0]), "checked": bool(item[1])} for item in items],
    }


def photo(url: str, caption: Optional[str] = None) -> Dict[str, Any]:
    """Build a photo block."""
    block: Dict[str, Any] = {
        "type": "photo",
        "photo": {"type": "photo", "media": str(url)},
    }
    if caption:
        block["caption"] = str(caption)
    return block


def animation(url: str, caption: Optional[str] = None) -> Dict[str, Any]:
    """Build an animation block."""
    block: Dict[str, Any] = {
        "type": "animation",
        "animation": {"type": "animation", "media": str(url)},
    }
    if caption:
        block["caption"] = str(caption)
    return block


def details(summary: str, body: str) -> Dict[str, Any]:
    """Build a details block."""
    return {"type": "details", "summary": str(summary), "text": str(body)}


def spoiler(text: str) -> Dict[str, Any]:
    """Build a spoiler block."""
    return {"type": "spoiler", "text": str(text)}


def button_grid(
    rows: Sequence[Sequence[Dict[str, Any]]],
    widths: Optional[Sequence[int]] = None,
) -> Dict[str, Any]:
    """Build a flattened buttons block with optional row widths."""
    flat: List[Dict[str, Any]] = []
    for row in rows:
        for btn in row:
            item: Dict[str, Any] = {"text": str(btn["text"])}
            if btn.get("callback_data") is not None:
                item["callback_data"] = str(btn["callback_data"])
            elif btn.get("url") is not None:
                item["url"] = str(btn["url"])
            if btn.get("style") is not None:
                item["style"] = str(btn["style"])
            flat.append(item)
    block: Dict[str, Any] = {"type": "buttons", "buttons": flat}
    if widths:
        block["widths"] = [int(width) for width in widths]
    return block


def rich_callback_button(text: str, callback_data: str, style: str = "primary") -> Dict[str, Any]:
    """Build a rich callback button and enforce Telegram's 64-byte limit."""
    data = str(callback_data)
    if len(data.encode("utf-8")) > 64:
        raise ValueError("callback_data exceeds Telegram's 64-byte limit")
    return {"text": str(text), "callback_data": data, "style": str(style)}


def rich_url_button(text: str, url: str, style: str = "primary") -> Dict[str, Any]:
    """Build a rich URL button."""
    return {"text": str(text), "url": str(url), "style": str(style)}


# Ergonomic aliases.
hr = divider
br = button_row
p = paragraph
h = heading


def validate_blocks(blocks: Sequence[Any]) -> List[str]:
    """Return list of error strings; empty means OK."""
    errors: List[str] = []
    for index, block in enumerate(blocks):
        if not isinstance(block, dict):
            errors.append(f"block[{index}]: not a dict ({type(block).__name__})")
            continue
        block_type = block.get("type")
        if not isinstance(block_type, str):
            errors.append(f"block[{index}]: missing/!str type")
        elif block_type not in _VALID_BLOCK_TYPES:
            errors.append(f"block[{index}]: unknown type {block_type!r}")
    return errors


def _is_transient(exc: BaseException) -> bool:
    """True if exc is likely transient (retry-worthy)."""
    if isinstance(exc, RichMessageError):
        message = str(exc).lower()
        return any(marker in message for marker in _TRANSIENT_MARKERS)
    if isinstance(exc, (requests.RequestException, ConnectionError, TimeoutError, OSError)):
        return True
    return False


def _normalize_buttons(buttons: Any) -> List[Dict[str, Any]]:
    """Accept button_row blocks, tuple form, or list of tuples."""
    if buttons is None or buttons == []:
        return []
    if isinstance(buttons, tuple) and buttons and isinstance(buttons[0], str):
        if len(buttons) < 2:
            raise ValueError("button tuple must contain at least label and callback_data")
        buttons = [buttons]

    out: List[Dict[str, Any]] = []
    for entry in buttons:
        if isinstance(entry, dict) and entry.get("type") == "buttons":
            out.append(entry)
            continue
        if isinstance(entry, (list, tuple)):
            row: List[Dict[str, Any]] = []
            if len(entry) >= 2 and not isinstance(entry[0], (dict, list, tuple)):
                label, data = entry[0], entry[1]
                style = entry[2] if len(entry) > 2 else "primary"
                row.append(rich_callback_button(label, data, style))
            else:
                for item in entry:
                    if isinstance(item, dict):
                        row.append(item)
                    elif isinstance(item, (list, tuple)) and len(item) >= 2:
                        label, data = item[0], item[1]
                        style = item[2] if len(item) > 2 else "primary"
                        row.append(rich_callback_button(label, data, style))
            if row:
                out.append(button_row(row))
    return out


def success_card(title: str, body: str, buttons: Any = None, footer: Optional[str] = None) -> List[Dict[str, Any]]:
    """Build a success card."""
    blocks: List[Dict[str, Any]] = [heading(f"✅ {title}"), paragraph(str(body))]
    if footer:
        blocks.append(paragraph(str(footer)))
    if buttons:
        blocks.extend(_normalize_buttons(buttons))
    return blocks


def error_card(title: str, body: str, hint: Optional[str] = None, buttons: Any = None, retry: Any = None) -> List[Dict[str, Any]]:
    """Build an error card, optionally with a retry callback button."""
    blocks: List[Dict[str, Any]] = [heading(f"❌ {title}"), paragraph(str(body))]
    if hint:
        blocks.append(paragraph(f"💡 {hint}"))
    if retry:
        label, data, *style_parts = retry
        style = style_parts[0] if style_parts and style_parts[0] else "primary"
        blocks.append(button_row([rich_callback_button(label, data, style)]))
    if buttons:
        blocks.extend(_normalize_buttons(buttons))
    return blocks


def progress_card(title: str, rows: Sequence[Sequence[Any]], buttons: Any = None) -> List[Dict[str, Any]]:
    """Build a progress card."""
    blocks: List[Dict[str, Any]] = [heading(f"⏳ {title}"), compact_table(["Field", "Value"], rows)]
    if buttons:
        blocks.extend(_normalize_buttons(buttons))
    return blocks


def stats_card(title: str, rows: Sequence[Sequence[Any]], buttons: Any = None) -> List[Dict[str, Any]]:
    """Build a statistics card."""
    blocks: List[Dict[str, Any]] = [heading(title), compact_table(["Metric", "Value"], rows)]
    if buttons:
        blocks.extend(_normalize_buttons(buttons))
    return blocks


def info_card(title: str, body: str, bullets: Optional[Sequence[str]] = None, buttons: Any = None) -> List[Dict[str, Any]]:
    """Build an information card."""
    blocks: List[Dict[str, Any]] = [heading(title), paragraph(str(body))]
    if bullets:
        blocks.append(bullet_list(bullets))
    if buttons:
        blocks.extend(_normalize_buttons(buttons))
    return blocks


def confirm_card(title: str, body: str, yes_label: str, yes_data: str, no_label: str = "❌ Cancel", no_data: str = "task_cancel") -> List[Dict[str, Any]]:
    """Build a yes/no confirmation card."""
    return [
        heading(title), paragraph(str(body)),
        button_row([
            rich_callback_button(yes_label, yes_data, "success"),
            rich_callback_button(no_label, no_data, "danger"),
        ]),
    ]


def wizard_card(step: int, total: int, title: str, body: str, buttons: Any = None, progress: Any = None) -> List[Dict[str, Any]]:
    """Build a wizard-step card."""
    blocks: List[Dict[str, Any]] = [heading(title), paragraph(f"Step {step}/{total} · {body}")]
    if progress is not None:
        blocks.append(compact_table(["Field", "Value"], [["Progress", f"{step}/{total}"], ["Status", str(progress)]]))
    if buttons:
        blocks.extend(_normalize_buttons(buttons))
    return blocks


def section_card(title: str, description: str, markup_or_buttons: Any, tail: Optional[str] = None) -> List[Dict[str, Any]]:
    """Build a section card from PTB-style markup or portable buttons."""
    blocks: List[Dict[str, Any]] = [heading(title), divider(), paragraph(str(description))]
    if tail:
        blocks.append(paragraph(str(tail)))
    if markup_or_buttons is not None:
        if hasattr(markup_or_buttons, "inline_keyboard"):
            for row in markup_or_buttons.inline_keyboard:
                row_buttons: List[Dict[str, Any]] = []
                for button in row:
                    button_url = getattr(button, "url", None)
                    if button_url:
                        row_buttons.append(rich_url_button(button.text, button_url, "primary"))
                    else:
                        row_buttons.append(rich_callback_button(button.text, getattr(button, "callback_data", None) or "menu", "primary"))
                if row_buttons:
                    blocks.append(button_row(row_buttons))
        else:
            blocks.extend(_normalize_buttons(markup_or_buttons))
    return blocks


def blocks_to_plain_text(blocks: Sequence[Dict[str, Any]]) -> str:
    """Best-effort plain-text rendering for editMessageText fallback."""
    parts: List[str] = []
    for block in blocks or []:
        if not isinstance(block, dict):
            continue
        block_type = block.get("type")
        if block_type == "heading":
            parts.append(f"*{block.get('text', '')}*")
        elif block_type == "paragraph":
            parts.append(str(block.get("text", "")))
        elif block_type == "divider":
            parts.append("―" * 12)
        elif block_type == "spacer":
            continue
        elif block_type == "quote":
            author = block.get("author")
            parts.append(f"> {block.get('text', '')}" + (f" — {author}" if author else ""))
        elif block_type == "code":
            language = block.get("language")
            text = str(block.get("text", ""))
            parts.append(f"```{language or ''}\n{text}\n```")
        elif block_type == "markdown":
            parts.append(str(block.get("text", "")))
        elif block_type == "list":
            parts.extend(f"• {item}" for item in block.get("items", []) or [])
        elif block_type == "checklist":
            for item in block.get("items", []) or []:
                if isinstance(item, dict):
                    mark = "☑" if item.get("checked") else "☐"
                    parts.append(f"{mark} {item.get('text', '')}")
        elif block_type == "table":
            for row in block.get("cells", []) or []:
                line = " | ".join(str(cell.get("text", "")) for cell in row if isinstance(cell, dict))
                if line.strip():
                    parts.append(line)
        elif block_type == "details":
            parts.append(f"▸ {block.get('summary', '')}")
            parts.append(str(block.get("text", "")))
        elif block_type == "spoiler":
            parts.append("(spoiler)")
        elif block_type == "video":
            parts.append("🎬 (video)")
        elif block_type == "photo":
            parts.append("🖼️ (photo)")
        elif block_type == "animation":
            parts.append("🎞️ (animation)")
        elif block_type == "buttons":
            continue
        elif "text" in block:
            parts.append(str(block["text"]))
    return "\n".join(parts).strip()


def blocks_to_inline_keyboard(blocks: Sequence[Dict[str, Any]]) -> Optional[Dict[str, Any]]:
    """Extract inline_keyboard from 'buttons' blocks."""
    rows: List[List[Dict[str, Any]]] = []
    for block in blocks or []:
        if not isinstance(block, dict) or block.get("type") != "buttons":
            continue
        row: List[Dict[str, Any]] = []
        for button in block.get("buttons", []) or []:
            if not isinstance(button, dict):
                continue
            item: Dict[str, Any] = {"text": str(button.get("text", ""))}
            if button.get("callback_data") is not None:
                item["callback_data"] = str(button["callback_data"])
            elif button.get("url") is not None:
                item["url"] = str(button["url"])
            row.append(item)
        if row:
            rows.append(row)
    return {"inline_keyboard": rows} if rows else None


def extract_message_id(resp: Any) -> Optional[int]:
    """Extract message_id from either an API response dict or PTB Message object."""
    if isinstance(resp, dict):
        inner = resp.get("result", resp)
        if isinstance(inner, dict):
            value = inner.get("message_id")
            try:
                return int(value) if value is not None else None
            except (TypeError, ValueError):
                return None
        return None
    value = getattr(resp, "message_id", None)
    try:
        return int(value) if value is not None else None
    except (TypeError, ValueError):
        return None


def build_photo_payload(
    chat_id: Any, photo_url: str, caption: Optional[str] = None,
    reply_markup: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    """Build a standard sendPhoto payload."""
    payload: Dict[str, Any] = {"chat_id": chat_id, "photo": str(photo_url)}
    if caption is not None:
        payload["caption"] = str(caption)
    if reply_markup is not None:
        payload["reply_markup"] = reply_markup
    return payload


def build_document_payload(
    chat_id: Any, document_url: str, caption: Optional[str] = None,
    reply_markup: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    """Build a standard sendDocument payload."""
    payload: Dict[str, Any] = {"chat_id": chat_id, "document": str(document_url)}
    if caption is not None:
        payload["caption"] = str(caption)
    if reply_markup is not None:
        payload["reply_markup"] = reply_markup
    return payload


class _CircuitBreaker:
    """Per-client circuit breaker."""

    def __init__(self, threshold: int, cooldown: int) -> None:
        self.threshold = max(1, int(threshold))
        self.cooldown = max(1, int(cooldown))
        self.fails = 0
        self.opened_at = 0.0

    def is_open(self) -> bool:
        if self.fails < self.threshold:
            return False
        if time.monotonic() - self.opened_at > self.cooldown:
            self.fails = self.threshold - 1
            return False
        return True

    def record_success(self) -> None:
        self.fails = 0
        self.opened_at = 0.0

    def record_failure(self) -> None:
        self.fails += 1
        if self.fails >= self.threshold and self.opened_at == 0.0:
            self.opened_at = time.monotonic()


class RichClient:
    """Portable rich-message client with all mutable state per instance."""

    def __init__(
        self,
        token: str,
        *,
        api_base: str = "https://api.telegram.org",
        timeout: int = 15,
        max_attempts: int = 3,
        backoff_base: float = 0.4,
        backoff_max: float = 4.0,
        max_concurrent: int = 8,
        circuit_threshold: int = 5,
        circuit_cooldown: int = 60,
        debug: bool = False,
    ) -> None:
        """Create a client. Numeric parameters are clamped to safe minimums."""
        if not token:
            raise ValueError("RichClient: token is required")
        self.token = str(token)
        self.api_base = str(api_base).rstrip("/")
        self.timeout = max(1, int(timeout))
        self.max_attempts = max(1, int(max_attempts))
        self.backoff_base = max(0.0, float(backoff_base))
        self.backoff_max = max(self.backoff_base, float(backoff_max))
        self.max_concurrent = max(1, int(max_concurrent))
        self.circuit_threshold = max(1, int(circuit_threshold))
        self.circuit_cooldown = max(1, int(circuit_cooldown))
        self.debug = bool(debug)

        self._session = requests.Session()
        self._session.headers.update({"User-Agent": "richmsg/1.1"})
        adapter = requests.adapters.HTTPAdapter(pool_connections=8, pool_maxsize=16, max_retries=0)
        self._session.mount("https://", adapter)
        self._session.mount("http://", adapter)

        self._breaker = _CircuitBreaker(self.circuit_threshold, self.circuit_cooldown)
        self._chat_locks: WeakValueDictionary[int, asyncio.Lock] = WeakValueDictionary()
        self._chat_locks_guard: Optional[asyncio.Lock] = None
        self._semaphore: Optional[asyncio.Semaphore] = None
        self._metrics: Dict[str, int] = {
            "sent": 0,
            "failed": 0,
            "fallback": 0,
            "circuit_skips": 0,
            "retry_attempts": 0,
            "stage_retries": 0,
        }

    def _get_semaphore(self) -> asyncio.Semaphore:
        """Lazily create the semaphore in the active loop context."""
        if self._semaphore is None:
            self._semaphore = asyncio.Semaphore(self.max_concurrent)
        return self._semaphore

    async def _get_chat_locks_guard(self) -> asyncio.Lock:
        """Lazily create the per-instance lock guard."""
        if self._chat_locks_guard is None:
            self._chat_locks_guard = asyncio.Lock()
        return self._chat_locks_guard

    def _call_api(self, method: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        """POST to Telegram Bot API and return its result dictionary."""
        url = f"{self.api_base}/bot{self.token}/{method}"
        response: Any = None
        try:
            if self.debug:
                logger.debug("POST %s payload=%r", self._redact(url), payload)
            response = self._session.post(url, json=payload, timeout=self.timeout)
            try:
                data = response.json()
            except Exception as exc:
                if self.debug:
                    logger.debug("raw response body=%r", getattr(response, "text", None))
                raise RichMessageError(
                    f"{method} returned invalid JSON (HTTP {response.status_code}): {exc}"
                ) from exc
        except RichMessageError:
            raise
        except requests.RequestException as exc:
            if self.debug:
                logger.debug("raw response body=%r", getattr(response, "text", None))
            raise RichMessageError(
                f"{method} request failed: {type(exc).__name__}: {exc}"
            ) from exc
        except Exception as exc:
            if self.debug:
                logger.debug("raw response body=%r", getattr(response, "text", None))
            raise RichMessageError(
                f"{method} request failed: {type(exc).__name__}: {exc}"
            ) from exc

        if self.debug:
            logger.debug("response HTTP %s JSON=%r", response.status_code, data)

        if not isinstance(data, dict) or not data.get("ok"):
            description = data.get("description") if isinstance(data, dict) else None
            if self.debug:
                logger.debug("RICH_PM: full error response=%r", data)
            retry_after: Optional[float] = None
            if response.status_code == 429:
                try:
                    retry_after = float(response.headers.get("Retry-After", 0)) or None
                except (TypeError, ValueError):
                    retry_after = None
            raise RichMessageError(
                f"{description or f'{method} failed'} (HTTP {response.status_code})",
                retry_after=retry_after,
            )

        result = data.get("result")
        return result if isinstance(result, dict) else {"result": result}

    def _redact(self, url: str) -> str:
        """Replace this client's token with <TOKEN> in a URL."""
        return str(url).replace(self.token, "<TOKEN>")

    def _circuit_open(self) -> bool:
        return self._breaker.is_open()

    def _record_success(self) -> None:
        self._breaker.record_success()

    def _record_failure(self) -> None:
        self._breaker.record_failure()

    async def _chat_lock(self, chat_id: int) -> asyncio.Lock:
        """Return an instance-local weak per-chat lock."""
        guard = await self._get_chat_locks_guard()
        async with guard:
            lock = self._chat_locks.get(chat_id)
            if lock is None:
                lock = asyncio.Lock()
                self._chat_locks[chat_id] = lock
            return lock

    async def _send_with_retry(
        self,
        chat_id: int,
        blocks: List[Dict[str, Any]],
        *,
        count_failure: bool = True,
    ) -> Dict[str, Any]:
        """Retry transient rich sends using exponential backoff."""
        delay = self.backoff_base
        last_exc: Optional[RichMessageError] = None
        for attempt in range(self.max_attempts):
            try:
                # FIX_RICH_SEND: try sendMessage with rich_message first.
                payload = {"chat_id": chat_id, "rich_message": {"blocks": blocks}}
                try:
                    response = await asyncio.to_thread(
                        self._call_api,
                        "sendMessage",
                        dict(payload),
                    )
                except RichMessageError as first_exc:
                    logger.warning(
                        "sendMessage with rich_message failed: %s. "
                        "Falling back to sendRichMessage.", first_exc
                    )
                    response = await asyncio.to_thread(
                        self._call_api,
                        "sendRichMessage",
                        dict(payload),
                    )
                self._metrics["sent"] += 1
                self._record_success()
                return response
            except RichMessageError as exc:
                last_exc = exc
                final = not _is_transient(exc) or attempt == self.max_attempts - 1
                if final:
                    if count_failure:
                        self._metrics["failed"] += 1
                    self._record_failure()
                    raise
                self._metrics["retry_attempts"] += 1
                retry_after = getattr(exc, "retry_after", None)
                sleep_for = max(delay, float(retry_after)) if retry_after else delay
                if sleep_for > 0:
                    await asyncio.sleep(sleep_for)
                delay = min(delay * 2.0, self.backoff_max)
        raise last_exc or RichMessageError("rich send failed")

    async def _send_with_media_strip(self, chat_id: int, blocks: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Retry once without media after a transient send failure."""
        try:
            return await self._send_with_retry(chat_id, blocks, count_failure=False)
        except RichMessageError as exc:
            if not _is_transient(exc):
                self._metrics["failed"] += 1
                raise
            stripped = [
                block for block in blocks
                if not (isinstance(block, dict) and block.get("type") in _STRIPPABLE_BLOCK_TYPES)
            ]
            if len(stripped) == len(blocks):
                self._metrics["failed"] += 1
                raise
            self._metrics["stage_retries"] += 1
            logger.warning("retrying without %d media block(s) after transient", len(blocks) - len(stripped))
            return await self._send_with_retry(chat_id, stripped, count_failure=True)

    async def _request_with_retry(
        self,
        method: str,
        payload: Dict[str, Any],
    ) -> Dict[str, Any]:
        """Retry a standard Bot API request using the same transport policy."""
        delay = self.backoff_base
        for attempt in range(self.max_attempts):
            try:
                response = await asyncio.to_thread(self._call_api, method, payload)
                self._metrics["sent"] += 1
                self._record_success()
                return response
            except RichMessageError as exc:
                if not _is_transient(exc) or attempt == self.max_attempts - 1:
                    self._metrics["failed"] += 1
                    self._record_failure()
                    raise
                self._metrics["retry_attempts"] += 1
                retry_after = getattr(exc, "retry_after", None)
                sleep_for = max(delay, float(retry_after)) if retry_after else delay
                if sleep_for > 0:
                    await asyncio.sleep(sleep_for)
                delay = min(delay * 2.0, self.backoff_max)
        raise RichMessageError(f"{method} failed")

    async def send(self, chat_id: int, blocks: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
        """Validate + circuit check + send with retry."""
        block_list = list(blocks)
        errors = validate_blocks(block_list)
        if errors:
            raise RichMessageValidationError(f"invalid blocks: {errors[0]}")
        if self._circuit_open():
            self._metrics["circuit_skips"] += 1
            raise RichMessageError("rich circuit open")
        async with self._get_semaphore():
            return await self._send_with_media_strip(chat_id, block_list)

    async def replace(self, chat_id: int, message_id: int, blocks: Sequence[Dict[str, Any]]) -> Dict[str, Any]:
        """3-stage replace: rich edit -> plain edit -> send new + delete old."""
        block_list = list(blocks)
        errors = validate_blocks(block_list)
        if errors:
            raise RichMessageValidationError(f"invalid blocks: {errors[0]}")
        if self._circuit_open():
            self._metrics["circuit_skips"] += 1
            raise RichMessageError("rich circuit open")

        lock = await self._chat_lock(chat_id)
        async with lock:
            async with self._get_semaphore():
                try:
                    response = await asyncio.to_thread(
                        self._call_api,
                        "editMessageText",
                        {"chat_id": chat_id, "message_id": message_id, "rich_message": {"blocks": block_list}},
                    )
                    self._metrics["sent"] += 1
                    self._record_success()
                    return response
                except Exception as exc:
                    self._metrics["stage_retries"] += 1
                    logger.debug("rich edit failed (%s)", str(exc)[:120])

                try:
                    reply_markup = blocks_to_inline_keyboard(block_list) or {"inline_keyboard": []}
                    response = await asyncio.to_thread(
                        self._call_api,
                        "editMessageText",
                        {
                            "chat_id": chat_id,
                            "message_id": message_id,
                            "text": blocks_to_plain_text(block_list) or "(updated)",
                            "parse_mode": "Markdown",
                            "reply_markup": reply_markup,
                        },
                    )
                    self._metrics["sent"] += 1
                    self._record_success()
                    return response
                except Exception as exc:
                    self._metrics["stage_retries"] += 1
                    logger.debug("plain edit failed (%s)", str(exc)[:120])

                try:
                    new_response = await self._send_with_media_strip(chat_id, block_list)
                except Exception:
                    raise
                try:
                    await asyncio.to_thread(self._call_api, "deleteMessage", {"chat_id": chat_id, "message_id": message_id})
                except Exception:
                    logger.debug("old message delete skipped")
                return new_response

    async def send_standard(self, method: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        """POST to any Telegram Bot API method with retry."""
        if not method or not isinstance(method, str):
            raise ValueError("method is required")
        if self._circuit_open():
            self._metrics["circuit_skips"] += 1
            raise RichMessageError("rich circuit open")
        async with self._get_semaphore():
            return await self._request_with_retry(method, dict(payload))

    async def edit_text(
        self,
        chat_id: int,
        message_id: int,
        text: str,
        reply_markup: Optional[Dict[str, Any]] = None,
        parse_mode: str = "Markdown",
    ) -> Dict[str, Any]:
        """Edit an existing message with plain text."""
        if self._circuit_open():
            self._metrics["circuit_skips"] += 1
            raise RichMessageError("rich circuit open")
        payload: Dict[str, Any] = {"chat_id": chat_id, "message_id": message_id, "text": str(text), "parse_mode": parse_mode}
        if reply_markup is not None:
            payload["reply_markup"] = reply_markup
        lock = await self._chat_lock(chat_id)
        async with lock:
            async with self._get_semaphore():
                return await self._request_with_retry("editMessageText", payload)

    async def delete(self, chat_id: int, message_id: int) -> Dict[str, Any]:
        """Delete a message with retry + circuit breaker."""
        if self._circuit_open():
            self._metrics["circuit_skips"] += 1
            raise RichMessageError("rich circuit open")
        lock = await self._chat_lock(chat_id)
        async with lock:
            async with self._get_semaphore():
                return await self._request_with_retry("deleteMessage", {"chat_id": chat_id, "message_id": message_id})

    async def send_or(
        self,
        chat_id: int,
        blocks: Sequence[Dict[str, Any]],
        fallback: Callable[..., Any],
        *,
        return_fallback_flag: bool = False,
    ) -> Any:
        """Try send; validation errors raise, all other errors use fallback."""
        try:
            response = await self.send(chat_id, blocks)
            return (response, False) if return_fallback_flag else response
        except RichMessageValidationError:
            logger.error("richmsg validation error — not falling back")
            raise
        except Exception as exc:
            self._metrics["fallback"] += 1
            if isinstance(exc, RichMessageError):
                logger.warning("rich send failed: %s", exc)
            else:
                logger.exception("rich send crashed")
            try:
                response = await fallback()
            except Exception:
                logger.exception("rich send fallback crashed")
                response = None
            return (response, True) if return_fallback_flag else response

    async def replace_or(
        self,
        chat_id: int,
        message_id: int,
        blocks: Sequence[Dict[str, Any]],
        fallback: Callable[..., Any],
        *,
        return_fallback_flag: bool = False,
    ) -> Any:
        """Try replace; validation errors raise, all other errors use fallback."""
        try:
            response = await self.replace(chat_id, message_id, blocks)
            return (response, False) if return_fallback_flag else response
        except RichMessageValidationError:
            logger.error("richmsg validation error — not falling back")
            raise
        except Exception as exc:
            self._metrics["fallback"] += 1
            if isinstance(exc, RichMessageError):
                logger.warning("rich replace failed: %s", exc)
            else:
                logger.exception("rich replace crashed")
            try:
                response = await fallback()
            except Exception:
                logger.exception("rich replace fallback crashed")
                response = None
            return (response, True) if return_fallback_flag else response

    async def tracked_send_or(
        self,
        context: Any,
        chat_id: int,
        blocks: Sequence[Dict[str, Any]],
        fallback: Callable[..., Any],
        track_key: str,
    ) -> Any:
        """send_or + store message_id in context.user_data[track_key]."""
        result = await self.send_or(chat_id, blocks, fallback)
        response = result[0] if isinstance(result, tuple) and len(result) == 2 else result
        message_id = extract_message_id(response)
        if message_id is not None and hasattr(context, "user_data"):
            context.user_data[track_key] = message_id
        return result

    async def tracked_replace_or(
        self,
        context: Any,
        chat_id: int,
        message_id: int,
        blocks: Sequence[Dict[str, Any]],
        fallback: Callable[..., Any],
        track_key: str,
    ) -> Any:
        """replace_or + store message_id in context.user_data[track_key]."""
        result = await self.replace_or(chat_id, message_id, blocks, fallback)
        response = result[0] if isinstance(result, tuple) and len(result) == 2 else result
        new_id = extract_message_id(response)
        if new_id is not None and hasattr(context, "user_data"):
            context.user_data[track_key] = new_id
        return result

    async def __aenter__(self) -> "RichClient":
        return self

    async def __aexit__(self, exc_type: Any, exc: Any, tb: Any) -> None:
        self.close()

    def close(self) -> None:
        """Close the HTTP session."""
        try:
            self._session.close()
        except Exception:
            pass

    def __repr__(self) -> str:
        return (
            f"RichClient(token=<TOKEN>..., "
            f"sent={self._metrics['sent']}, "
            f"failed={self._metrics['failed']}, "
            f"circuit={'open' if self._circuit_open() else 'closed'})"
        )

    def metrics(self) -> Dict[str, int]:
        """Return a snapshot: sent/failed are final operations; retry_attempts counts extra attempts; stage_retries counts rich→plain→send transitions; fallback counts *_or fallback calls; circuit_skips counts calls rejected by an open circuit."""
        return dict(self._metrics)


__all__ = [
    "RichMessageError", "RichMessageValidationError",
    "heading", "paragraph", "video", "compact_table", "button_row",
    "divider", "spacer", "quote", "code", "markdown", "bullet_list",
    "checklist", "photo", "animation", "details", "spoiler", "button_grid",
    "rich_callback_button", "rich_url_button",
    "validate_blocks",
    "success_card", "error_card", "progress_card", "stats_card", "info_card",
    "confirm_card", "wizard_card", "section_card",
    "blocks_to_plain_text", "blocks_to_inline_keyboard", "extract_message_id",
    "build_photo_payload", "build_document_payload",
    "hr", "br", "p", "h",
    "RichClient",
]
