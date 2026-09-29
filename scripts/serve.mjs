// Tiny static server for the web build: node scripts/serve.mjs [port]
import http from "node:http";
import fs from "node:fs";
import path from "node:path";

const ROOT = path.resolve("web");
const TYPES = { ".html": "text/html; charset=utf-8", ".js": "text/javascript", ".css": "text/css", ".woff2": "font/woff2", ".txt": "text/plain" };
export function serve(port = 8080) {
  return http.createServer((req, res) => {
    const url = decodeURIComponent(new URL(req.url, "http://x").pathname);
    const file = path.join(ROOT, url.endsWith("/") ? url + "index.html" : url);
    if (!file.startsWith(ROOT) || !fs.existsSync(file) || fs.statSync(file).isDirectory()) { res.writeHead(404); return res.end("not found"); }
    res.writeHead(200, { "content-type": TYPES[path.extname(file)] ?? "application/octet-stream" });
    fs.createReadStream(file).pipe(res);
  }).listen(port);
}
if (import.meta.url === `file://${process.argv[1]}`) {
  const port = Number(process.argv[2]) || 8080;
  serve(port);
  console.log(`Hopscraper: http://localhost:${port}/`);
}
