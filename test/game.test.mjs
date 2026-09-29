// Runs the real game in Chromium and checks the simulation through the window.__hop handle.
import { test, before, after } from "node:test";
import assert from "node:assert/strict";
import { chromium, devices } from "playwright";
import { serve } from "../scripts/serve.mjs";

const PORT = 8391, URL = `http://localhost:${PORT}/`;
let server, browser, page;
const errors = [];

before(async () => {
  server = serve(PORT);
  browser = await chromium.launch();
  page = await browser.newPage({ viewport: { width: 1280, height: 960 } });
  page.on("pageerror", (e) => errors.push(e.message));
  await page.goto(URL);
  await page.waitForFunction(() => window.__hop);
});
after(async () => { await browser?.close(); server?.close(); });

/** plays `ticks` frames of a fresh game with the built-in bot, returns score, floor and the recorded input bits */
const botRun = (seed, ticks) => page.evaluate(([seed, ticks]) => {
  const { newGame, stepGame, Bot, gameScore } = window.__hop;
  const g = newGame(seed, true), mind = {}, input = [];
  for (let i = 0; i < ticks && g.state !== "dead"; i++) { const b = Bot.think(g, mind); input.push(b); stepGame(g, b); g.ev.length = 0; }
  return { score: gameScore(g), best: g.best, tick: g.tick, state: g.state, x: g.p.x, y: g.p.y, input };
}, [seed, ticks]);

test("boots to the title screen without errors", async () => {
  await page.waitForTimeout(800);
  assert.equal(await page.evaluate(() => window.__hop.App.screen), "title");
  assert.deepEqual(errors, []);
});

test("the tower is generated from the seed: same seed, same floors", async () => {
  const a = await botRun(12345, 2000), b = await botRun(12345, 2000), c = await botRun(999, 2000);
  assert.equal(a.score, b.score);
  assert.equal(a.x, b.x);
  assert.equal(a.y, b.y);
  assert.notDeepEqual([a.x, a.y, a.score], [c.x, c.y, c.score]);
});

test("the bot climbs the tower", async () => {
  const r = await botRun(2026, 6000);
  assert.ok(r.best >= 40, `bot reached floor ${r.best}`);
});

test("a replay code re-runs to exactly the same result", async () => {
  const r = await botRun(777, 3000);
  const same = await page.evaluate(([seed, bits]) => {
    const { newGame, stepGame, gameScore, replayToCode, replayFromCode } = window.__hop;
    // run-length encoding used by the game's replay format: letter = input bits, base-36 = run length
    let s = "", prev = -1, run = 0;
    for (const b of bits) { if (b === prev) run++; else { if (run) s += "ABCDEFGH"[prev] + run.toString(36); prev = b; run = 1; } }
    if (run) s += "ABCDEFGH"[prev] + run.toString(36);
    const code = replayToCode({ v: 1, seed, rejump: true, input: s, name: "TEST", score: 0, char: 0 });
    const rep = replayFromCode(code);
    const g = newGame(rep.seed, rep.rejump);
    let k = 0;
    for (const m of rep.input.matchAll(/([A-H])([0-9a-z]+)/g)) for (let i = 0; i < parseInt(m[2], 36); i++, k++) { stepGame(g, m[1].charCodeAt(0) - 65); g.ev.length = 0; }
    return { score: gameScore(g), k };
  }, [777, r.input]);
  assert.equal(same.k, r.input.length);
  assert.equal(same.score, r.score);
});

test("rejects broken replay codes", async () => {
  const res = await page.evaluate(() => {
    const out = [];
    for (const c of ["", "HELLO", "HOPR1-!!!", "HOPR1-" + btoa(JSON.stringify({ v: 1, seed: 1, input: "Z9", name: "x", score: 1 }))]) {
      try { window.__hop.replayFromCode(c); out.push("ok"); } catch { out.push("err"); }
    }
    return out;
  });
  assert.deepEqual(res, ["err", "err", "err", "err"]);
});

test("shows on-screen buttons on a touch phone", async () => {
  const ctx = await browser.newContext({ ...devices["iPhone 13"] });
  const p = await ctx.newPage();
  await p.goto(URL);
  await p.waitForFunction(() => window.__hop);
  await p.touchscreen.tap(195, 400);
  assert.equal(await p.evaluate(() => document.body.classList.contains("touch-on")), false); // not on the title screen
  await p.evaluate(() => window.__hop.startGame());
  await p.waitForFunction(() => document.body.classList.contains("touch-on"), null, { timeout: 5000 });
  assert.equal(await p.locator("#touch .tbtn").count(), 3);
  await ctx.close();
});
