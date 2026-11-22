// Live feed race: when does each source first show each goal and assist, compared with FPL?
// usage: node feedrace.js GW            (runs until every fixture of the GW is finished, polling only during matches)
// writes ledger/race-GW.json (raw first-seen times, survives restarts) and out/feedrace.json (rows for the lab dashboard)
const fs = require('fs'); const path = require('path');
// GitHub Actions: no GW argument = the gameweek in progress (or the next one). RACE_DIR = where ledger/ and out/ live.
// RACE_MAX_MIN stops after that many minutes; RACE_IDLE_MIN exits when no match is live or starting within that many minutes.
let GW = +process.argv[2];
const DIR = process.env.RACE_DIR || __dirname, MAXMIN = +process.env.RACE_MAX_MIN || 0, IDLEMIN = +process.env.RACE_IDLE_MIN || 0, T0 = Date.now();
let LED, OUT;
const UA = { 'user-agent': 'Mozilla/5.0' };
const get = async (u, ms = 9000) => { const c = new AbortController(); const t = setTimeout(() => c.abort(), ms); try { const r = await fetch(u, { headers: UA, signal: c.signal }); if (!r.ok) throw new Error('HTTP ' + r.status); return await r.json(); } finally { clearTimeout(t); } };
const FPL = 'https://fantasy.premierleague.com/api/', PLA = 'https://footballapi.pulselive.com/football/', FMA = 'https://www.fotmob.com/api/data/';
const SRC = ['fpl', 'espn', 'pl', 'fotmob'];
let S;
const save = () => { fs.writeFileSync(LED, JSON.stringify(S)); fs.writeFileSync(OUT, JSON.stringify(rows())); };
const seen = (src, fx, metric, n, extra) => { for (let k = 1; k <= n; k++) { const key = `${fx}|${metric}|${k}`; const e = S.first[key] || (S.first[key] = {}); if (!e[src]) { e[src] = Date.now(); if (extra && k === n) e.min = e.min || extra; } } };
const ALIAS = { 'brighton and hove albion': 'brighton', 'wolverhampton wanderers': 'wolves', 'tottenham hotspur': 'spurs', 'nottingham forest': "nott'm forest", 'manchester city': 'man city', 'manchester united': 'man utd', 'afc bournemouth': 'bournemouth', 'west ham united': 'west ham', 'newcastle united': 'newcastle', 'leeds united': 'leeds', 'leicester city': 'leicester', 'ipswich town': 'ipswich', 'hull city': 'hull', 'coventry city': 'coventry', 'sheffield united': 'sheffield utd', 'luton town': 'luton', 'norwich city': 'norwich', 'stoke city': 'stoke', 'cardiff city': 'cardiff', 'swansea city': 'swansea', 'west bromwich albion': 'west brom', 'queens park rangers': 'qpr' };
let TEAMS = [];
const team = (name) => { const n = String(name || '').toLowerCase().replace(/&/g, 'and').trim(); const a = ALIAS[n] || n; const st = (x) => x.replace(/\b(fc|afc)\b/g, '').replace(/[^a-z']/g, ''); const t = TEAMS.find((x) => x.name.toLowerCase() === a || st(x.name.toLowerCase()) === st(a) || st(x.name.toLowerCase()) === st(n)); return t ? t.id : null; };
let FX = [], PLIDX = null;
const live = () => process.env.RACE_ALL ? FX : FX.filter((f) => { const k = Date.parse(f.kickoff_time); return Date.now() >= k - 120e3 && Date.now() < k + 150 * 60e3 && !(f.finished && S.done && S.done[f.id]); });
const tag = (f) => { const T = (id) => (TEAMS.find((t) => t.id === id) || {}).short_name; return `${T(f.team_h)}-${T(f.team_a)}`; };

async function pollFpl(L) {
  const fx = await get(FPL + 'fixtures/?event=' + GW); FX = fx;
  fx.filter((f) => L.some((x) => x.id === f.id)).forEach((f) => {
    seen('fpl', f.id, 'goal', (f.team_h_score || 0) + (f.team_a_score || 0));
    const as = (f.stats || []).find((s) => s.identifier === 'assists'); const na = as ? [...as.h, ...as.a].reduce((a, x) => a + x.value, 0) : 0; seen('fpl', f.id, 'assist', na);
    if (f.finished) (S.done = S.done || {})[f.id] = true; });
}
async function pollEspn(L) {
  const sb = await get('https://site.api.espn.com/apis/site/v2/sports/soccer/eng.1/scoreboard');
  (sb.events || []).forEach((ev) => { const c = (ev.competitions || [])[0]; if (!c) return; const H = c.competitors.find((x) => x.homeAway === 'home'), A = c.competitors.find((x) => x.homeAway === 'away');
    const f = L.find((x) => x.team_h === team(H.team.displayName) && x.team_a === team(A.team.displayName)); if (!f) return;
    seen('espn', f.id, 'goal', (+H.score || 0) + (+A.score || 0), ev.status && ev.status.displayClock); });
}
async function plIndex() {
  if (PLIDX && FX.every((f) => PLIDX[f.id] !== undefined)) return PLIDX;
  const cs = await get(PLA + 'competitions/1/compseasons?page=0&pageSize=5'); const sid = cs.content[0].id;
  const ks = FX.map((f) => Date.parse(f.kickoff_time)); const d = (x) => new Date(x).toISOString().slice(0, 10);
  const fl = await get(PLA + `fixtures?comps=1&compSeasons=${sid}&page=0&pageSize=40&sort=asc&startDate=${d(Math.min(...ks) - 864e5)}&endDate=${d(Math.max(...ks) + 864e5)}&altIds=true`);
  PLIDX = {}; FX.forEach((f) => { const k = Date.parse(f.kickoff_time); const hit = (fl.content || []).find((x) => { const t = x.teams || []; if (t.length < 2) return false; const ab = (i) => (TEAMS.find((y) => y.short_name === ((t[i].team.club || {}).abbr)) || { id: team(t[i].team.name) }).id; return ab(0) === f.team_h && ab(1) === f.team_a && Math.abs((x.kickoff && x.kickoff.millis || 0) - k) < 6 * 36e5; }); PLIDX[f.id] = hit ? hit.id : null; });
  return PLIDX;
}
async function pollPl(L) {
  const idx = await plIndex();
  await Promise.all(L.filter((f) => idx[f.id]).map(async (f) => { const d = await get(PLA + 'fixtures/' + idx[f.id] + '?altIds=true');
    const t = d.teams || []; seen('pl', f.id, 'goal', (t[0] ? +t[0].score || 0 : 0) + (t[1] ? +t[1].score || 0 : 0), d.clock && d.clock.label);
    seen('pl', f.id, 'assist', (d.events || []).filter((x) => (x.type === 'G' || x.type === 'P') && x.assistId).length); }));
}
const FMD = {};
async function pollFotmob(L) {
  const days = [...new Set(L.map((f) => f.kickoff_time.slice(0, 10).replace(/-/g, '')))]; const ms = [];
  for (const d of days) { const j = await get(FMA + 'matches?date=' + d); (j.leagues || []).forEach((l) => { if (l.primaryId === 47 || l.id === 47) ms.push(...(l.matches || [])); }); }
  await Promise.all(L.map(async (f) => { const m = ms.find((x) => x.home && x.away && team(x.home.name) === f.team_h && team(x.away.name) === f.team_a); if (!m) return;
    const g = (+m.home.score || 0) + (+m.away.score || 0); seen('fotmob', f.id, 'goal', g, m.status && m.status.liveTime && m.status.liveTime.short);
    const o = FMD[f.id] || (FMD[f.id] = {}); if (m.status && m.status.started && (o.g !== g || Date.now() - (o.at || 0) > 60e3)) { o.g = g; o.at = Date.now();
      const d = await get(FMA + 'matchDetails?matchId=' + m.id, 15000); const ev = (((d.content || {}).matchFacts || {}).events || {}).events || [];
      seen('fotmob', f.id, 'assist', ev.filter((x) => x.type === 'Goal' && !x.ownGoal && (x.assistPlayerId || x.assistInput)).length); } }));
}
function rows() {
  const out = []; Object.entries(S.first).forEach(([key, e]) => { const [fx, metric, n] = key.split('|'); const f = FX.find((x) => x.id === +fx); if (!f) return;
    const firstAt = Math.min(...SRC.filter((s) => e[s]).map((s) => e[s])); const winners = SRC.filter((s) => e[s] && e[s] - firstAt < 5e3);
    const lead = (s) => (e[s] && e.fpl ? Math.round((e.fpl - e[s]) / 1000) : null);
    out.push({ gw: GW, match: tag(f), fixture: +fx, metric, n: +n, minute: e.min || '', fpl_at: e.fpl ? new Date(e.fpl).toISOString() : null,
      espn_lead_s: metric === 'goal' ? lead('espn') : null, pl_lead_s: lead('pl'), fotmob_lead_s: lead('fotmob'), first: winners.join('+') }); });
  return out.sort((a, b) => (a.fpl_at || '9').localeCompare(b.fpl_at || '9'));
}
(async () => {
  const bs = await get(FPL + 'bootstrap-static/'); TEAMS = bs.teams;
  if (!GW) { const ev = bs.events.find((e) => e.is_current && !e.finished) || bs.events.find((e) => e.is_next); if (!ev) { console.error('no gameweek in progress'); return; } GW = ev.id; }
  LED = path.join(DIR, 'ledger', `race-${GW}.json`); OUT = path.join(DIR, 'out', `feedrace-${GW}.json`);
  fs.mkdirSync(path.dirname(LED), { recursive: true }); fs.mkdirSync(path.dirname(OUT), { recursive: true });
  S = fs.existsSync(LED) ? JSON.parse(fs.readFileSync(LED, 'utf8')) : { gw: GW, first: {}, polls: {}, errors: {}, started: new Date().toISOString() };
  FX = await get(FPL + 'fixtures/?event=' + GW);
  console.error(`race GW${GW}: ${FX.length} fixtures; ledger ${LED}`);
  let n = 0;
  for (;;) {
    if (FX.length && FX.every((f) => S.done && S.done[f.id])) { await new Promise((r) => setTimeout(r, 1)); break; }
    if (MAXMIN && Date.now() - T0 > MAXMIN * 60e3) { save(); console.error('time limit reached; the next run resumes from the ledger'); return; }
    const L = live();
    if (!L.length && IDLEMIN) { const soon = FX.some((f) => { const k = Date.parse(f.kickoff_time); return !(S.done && S.done[f.id]) && k > Date.now() - 150 * 60e3 && k - 120e3 - Date.now() < IDLEMIN * 60e3; }); if (!soon) { save(); console.error('no match live or starting soon; exiting'); return; } }
    if (!L.length) { const next = FX.filter((f) => !(S.done && S.done[f.id])).map((f) => Date.parse(f.kickoff_time) - 120e3 - Date.now()).filter((x) => x > 0).sort((a, b) => a - b)[0];
      const wait = Math.min(next == null ? 600e3 : next, 600e3); if (next == null) { try { FX = await get(FPL + 'fixtures/?event=' + GW); FX.forEach((f) => { if (f.finished) (S.done = S.done || {})[f.id] = true; }); save(); } catch (e) {} } await new Promise((r) => setTimeout(r, Math.max(5e3, wait))); continue; }
    n++; const jobs = { fpl: pollFpl, espn: pollEspn, fotmob: pollFotmob }; if (n % 2) jobs.pl = pollPl;
    await Promise.all(Object.entries(jobs).map(async ([s, fn]) => { try { await fn(L); S.polls[s] = (S.polls[s] || 0) + 1; } catch (e) { S.errors[s] = (S.errors[s] || 0) + 1; S.lastErr = `${s}: ${e.message}`; } }));
    S.at = new Date().toISOString(); save();
    if (n % 30 === 0) console.error(new Date().toISOString(), L.map(tag).join(' '), 'keys', Object.keys(S.first).length, JSON.stringify(S.errors));
    if (process.env.RACE_ONCE && n >= 2) break;
    await new Promise((r) => setTimeout(r, 10e3));
  }
  S.finished = new Date().toISOString(); save(); console.error('race done'); console.log(JSON.stringify(rows(), null, 1));
})();
