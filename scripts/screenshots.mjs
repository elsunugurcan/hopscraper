// Real screenshots for the README: title screen, a live run played by the built-in bot, touch layout on a phone.
//   node scripts/screenshots.mjs
import fs from "node:fs";
import { chromium, devices } from "playwright";
import { serve } from "./serve.mjs";

const PORT = 8392, URL = `http://localhost:${PORT}/`;
const server = serve(PORT);
fs.mkdirSync("screenshots", { recursive: true });
const browser = await chromium.launch();
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const shot = (p, name) => p.screenshot({ path: `screenshots/${name}.jpg`, type: "jpeg", quality: 86 });

const page = await browser.newPage({ viewport: { width: 1280, height: 960 } });
await page.goto(URL);
await page.waitForFunction(() => window.__hop);
await sleep(2500);
await shot(page, "title");

// live game driven by the built-in bot through a virtual gamepad (the game reads it like a real controller)
await page.evaluate(() => {
  const mind = {};
  navigator.getGamepads = () => {
    const h = window.__hop, s = h.App.sess;
    const b = s && s.g.state === "play" ? h.Bot.think(s.g, mind) : 0;
    const btn = (on) => ({ pressed: on, value: on ? 1 : 0 });
    return [{ connected: true, axes: [b & 1 ? -1 : b & 2 ? 1 : 0, 0], buttons: [btn(!!(b & 4)), ...Array.from({ length: 15 }, () => btn(false))] }];
  };
  window.__hop.startGame();
});
let elapsed = 0;
for (const [name, at] of [["play-1", 9000], ["play-2", 24000], ["play-3", 40000]]) {
  await sleep(at - elapsed); elapsed = at;
  await shot(page, name);
}
console.log("floor", await page.evaluate(() => window.__hop.App.sess.g.best));

const ctx = await browser.newContext({ ...devices["iPhone 13"] });
const phone = await ctx.newPage();
await phone.goto(URL);
await phone.waitForFunction(() => window.__hop);
await phone.touchscreen.tap(195, 400);
await phone.evaluate(() => window.__hop.startGame());
await sleep(2500);
await shot(phone, "phone");

await browser.close();
server.close();
console.log("screenshots/ ✓");
