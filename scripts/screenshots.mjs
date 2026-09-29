// Real screenshots for the README: title screen, a bot run watched as a replay, touch layout on a phone.
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

// let the built-in bot climb, then watch its run as a replay
const code = await page.evaluate(() => {
  const { newGame, stepGame, Bot, gameScore, replayToCode } = window.__hop;
  const g = newGame(424242, true), mind = {}, bits = [];
  for (let i = 0; i < 9000 && g.state !== "dead"; i++) { const b = Bot.think(g, mind); bits.push(b); stepGame(g, b); g.ev.length = 0; }
  let s = "", prev = -1, run = 0;
  for (const b of bits) { if (b === prev) run++; else { if (run) s += "ABCDEFGH"[prev] + run.toString(36); prev = b; run = 1; } }
  if (run) s += "ABCDEFGH"[prev] + run.toString(36);
  return replayToCode({ v: 1, seed: 424242, rejump: true, input: s, name: "BOT", score: gameScore(g), char: 1 });
});
await page.evaluate((c) => window.__hop.startReplay(window.__hop.replayFromCode(c), "title"), code);
for (const [name, ms] of [["play-1", 9000], ["play-2", 14000], ["play-3", 20000]]) {
  await sleep(ms - (name === "play-1" ? 0 : 0));
  await shot(page, name);
}

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
