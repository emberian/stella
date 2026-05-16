//! Minimal single-threaded HTTP server (stdlib only).
//!
//! Serves the stella-viz single-page UI on `http://127.0.0.1:<port>`.
//!
//! Routes:
//!   GET /          → HTML shell
//!   GET /api/presets  → JSON array of preset names+descriptions
//!   GET /api/dot/<n>  → JSON { dep_graph_dot, execution_summary } for preset n

use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};

use crate::presets::all_presets;

// ─────────────────────────────────────────────────────────────────────────────
// HTML page (embedded)
// ─────────────────────────────────────────────────────────────────────────────

static HTML: &str = include_str!("ui.html");

// ─────────────────────────────────────────────────────────────────────────────
// HTTP helpers
// ─────────────────────────────────────────────────────────────────────────────

fn http_ok(stream: &mut TcpStream, content_type: &str, body: &str) {
    let response = format!(
        "HTTP/1.1 200 OK\r\n\
         Content-Type: {content_type}; charset=utf-8\r\n\
         Content-Length: {len}\r\n\
         Access-Control-Allow-Origin: *\r\n\
         Connection: close\r\n\
         \r\n\
         {body}",
        len = body.len()
    );
    let _ = stream.write_all(response.as_bytes());
}

fn http_not_found(stream: &mut TcpStream) {
    let body = "404 Not Found";
    let response = format!(
        "HTTP/1.1 404 Not Found\r\n\
         Content-Type: text/plain\r\n\
         Content-Length: {len}\r\n\
         Connection: close\r\n\
         \r\n\
         {body}",
        len = body.len()
    );
    let _ = stream.write_all(response.as_bytes());
}

// ─────────────────────────────────────────────────────────────────────────────
// Simple JSON escaping (no external crate)
// ─────────────────────────────────────────────────────────────────────────────

fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"'  => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Request handler
// ─────────────────────────────────────────────────────────────────────────────

fn handle(mut stream: TcpStream) {
    let mut buf = [0u8; 4096];
    let n = match stream.read(&mut buf) {
        Ok(n) => n,
        Err(_) => return,
    };
    let raw = std::str::from_utf8(&buf[..n]).unwrap_or("");
    let first_line = raw.lines().next().unwrap_or("");
    let parts: Vec<&str> = first_line.split_whitespace().collect();
    if parts.len() < 2 {
        return;
    }
    let path = parts[1];

    let presets = all_presets();

    if path == "/" || path == "/index.html" {
        http_ok(&mut stream, "text/html", HTML);
        return;
    }

    if path == "/api/presets" {
        let items: Vec<String> = presets
            .iter()
            .enumerate()
            .map(|(i, p)| {
                format!(
                    "{{\"id\":{i},\"name\":{},\"description\":{}}}",
                    json_str(&p.name),
                    json_str(&p.description)
                )
            })
            .collect();
        let body = format!("[{}]", items.join(","));
        http_ok(&mut stream, "application/json", &body);
        return;
    }

    if let Some(rest) = path.strip_prefix("/api/dot/") {
        if let Ok(idx) = rest.parse::<usize>() {
            if idx < presets.len() {
                let p = &presets[idx];
                let body = format!(
                    "{{\"name\":{},\"dep_graph_dot\":{},\"execution_summary\":{}}}",
                    json_str(&p.name),
                    json_str(&p.dep_graph_dot),
                    json_str(&p.execution_summary)
                );
                http_ok(&mut stream, "application/json", &body);
                return;
            }
        }
    }

    http_not_found(&mut stream);
}

// ─────────────────────────────────────────────────────────────────────────────
// Server entry point
// ─────────────────────────────────────────────────────────────────────────────

/// Start the HTTP server on `127.0.0.1:port`. Returns the bound port.
pub fn serve(port: u16) -> std::io::Result<()> {
    let addr = format!("127.0.0.1:{port}");
    let listener = TcpListener::bind(&addr)?;
    eprintln!("stella-viz: listening on http://{addr}");
    eprintln!("Open your browser at: http://{addr}");
    eprintln!("Press Ctrl-C to stop.");
    for stream in listener.incoming() {
        match stream {
            Ok(s) => handle(s),
            Err(e) => eprintln!("connection error: {e}"),
        }
    }
    Ok(())
}
