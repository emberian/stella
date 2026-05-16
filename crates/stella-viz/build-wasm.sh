#!/usr/bin/env bash
# build-wasm.sh — build stella-viz as a WASM/ES-module for the static GitHub Pages site.
#
# Toolchain requirements
# ──────────────────────
#   rustup target add wasm32-unknown-unknown
#   cargo install wasm-pack            # https://rustwasm.github.io/wasm-pack/
#
# If neither is installed yet, this script will tell you and exit 1.
# The Rust source + web/ HTML are fully written; only the build step is gated.
#
# Usage
# ─────
#   cd crates/stella-viz
#   ./build-wasm.sh           # produces web/pkg/
#   # Then open web/index.html in a browser (or serve with any static server).
#
# GitHub Pages deployment
# ───────────────────────
#   The web/ directory is self-contained: copy it to your Pages branch root,
#   or configure the Pages source as crates/stella-viz/web/ and push.
#   No server is required — the Rust engine runs entirely in the browser.
#
# Native server (unchanged)
# ─────────────────────────
#   cargo build -p stella-viz           # still builds the TCP server target

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "==> stella-viz WASM build"

# ── Check wasm-pack ────────────────────────────────────────────────────────────
if ! command -v wasm-pack &>/dev/null; then
    echo ""
    echo "ERROR: wasm-pack not found."
    echo "Install it with:"
    echo "    cargo install wasm-pack"
    echo "and ensure ~/.cargo/bin is on your PATH, then re-run this script."
    exit 1
fi

# ── Check wasm32 target ────────────────────────────────────────────────────────
if ! rustup target list --installed 2>/dev/null | grep -q "wasm32-unknown-unknown"; then
    echo ""
    echo "ERROR: wasm32-unknown-unknown target not installed."
    echo "Install it with:"
    echo "    rustup target add wasm32-unknown-unknown"
    echo "then re-run this script."
    exit 1
fi

echo "    wasm-pack: $(wasm-pack --version)"
echo "    target:    wasm32-unknown-unknown"
echo ""

# ── Build ──────────────────────────────────────────────────────────────────────
# --target web   : generates an ES module (import/export), suitable for static pages.
# --out-dir      : output goes to web/pkg/ so index.html can import it directly.
# --features wasm: enables the wasm-bindgen bindings in src/wasm.rs.
# --no-typescript: skip .d.ts generation (not needed for the static site).
# --release      : optimised build (smaller WASM, faster startup).

echo "==> Running wasm-pack build --target web --release …"

wasm-pack build \
    --target web \
    --out-dir web/pkg \
    --release \
    -- \
    --features wasm \
    --no-default-features

echo ""
echo "==> Build complete.  Output:"
ls -lh web/pkg/*.wasm web/pkg/*.js 2>/dev/null || ls -lh web/pkg/

echo ""
echo "==> To view locally (any static-file server works):"
echo "    python3 -m http.server 8080 --directory web/"
echo "    # then open http://localhost:8080/"
echo ""
echo "==> To deploy to GitHub Pages:"
echo "    # Option A: copy web/ to the root of your gh-pages branch."
echo "    # Option B: set Pages source to crates/stella-viz/web/ in repo settings."
echo "    # The pkg/ directory must be committed (or the CI build step added)."
echo ""
echo "==> Native TCP server still builds normally:"
echo "    cargo build -p stella-viz"
