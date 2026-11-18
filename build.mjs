// Builds the APA 7 reference list from the Zotero citations in the PhD documents
// named in sources.json, plus manual.json (references with no Zotero field) and
// overrides.json (corrections to Zotero data). Writes README.md, index.html,
// references.json and build-info.json, and a local check-report.md.
//
// Run: node build.mjs

import { readFileSync, writeFileSync, readdirSync, statSync, existsSync } from 'node:fs'
import { execFileSync } from 'node:child_process'
import { join, dirname } from 'node:path'
import { homedir } from 'node:os'
import { createHash } from 'node:crypto'
import { fileURLToPath } from 'node:url'
import { Cite, plugins } from '@citation-js/core'
import '@citation-js/plugin-csl'

const here = dirname(fileURLToPath(import.meta.url))
const read = (f, fallback) => (existsSync(join(here, f)) ? JSON.parse(readFileSync(join(here, f), 'utf8')) : fallback)

const sources = read('sources.json')
const manual = read('manual.json', [])
const overrides = read('overrides.json', { fix: {}, merge: [], exclude: [] })
const root = sources.root.replace(/^~/, homedir())

// ---------- pick the newest version of each document ----------
function pickDocument(doc) {
  const folder = join(root, doc.folder)
  const re = new RegExp(doc.match)
  const files = readdirSync(folder)
    .filter((f) => re.test(f))
    .map((f) => ({ f, v: Number(f.match(re)[1]), m: statSync(join(folder, f)).mtimeMs }))
    .sort((a, b) => b.v - a.v || b.m - a.m)
  if (!files.length) throw new Error(`No file matching ${doc.match} in ${folder}`)
  return { ...doc, file: files[0].f, version: files[0].v, path: join(folder, files[0].f) }
}

// ---------- docx reading ----------
const decode = (s) =>
  s.replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&quot;/g, '"').replace(/&apos;/g, "'").replace(/&#(\d+);/g, (_, n) => String.fromCodePoint(Number(n))).replace(/&amp;/g, '&')

function docxXml(path) {
  const parts = []
  for (const part of ['word/document.xml', 'word/footnotes.xml', 'word/endnotes.xml']) {
    try {
      parts.push(execFileSync('unzip', ['-p', path, part], { maxBuffer: 64 * 1024 * 1024 }).toString('utf8'))
    } catch {
      /* part not present */
    }
  }
  return parts.join('\n')
}

function zoteroItems(xml) {
  const items = []
  const tok = /<w:fldChar\b[^>]*w:fldCharType="(begin|separate|end)"[^>]*\/?>|<w:instrText\b[^>]*>([^<]*)<\/w:instrText>/g
  let inside = false
  let buf = []
  for (const m of xml.matchAll(tok)) {
    if (m[1] === 'begin') {
      inside = true
      buf = []
    } else if (m[1] && inside) {
      inside = false
      const code = decode(buf.join(''))
      if (code.includes('ZOTERO_ITEM')) {
        const data = JSON.parse(code.slice(code.indexOf('{')))
        for (const ci of data.citationItems || []) if (ci.itemData) items.push(ci.itemData)
      }
    } else if (m[2] !== undefined && inside) {
      buf.push(m[2])
    }
  }
  return items
}

function paragraphs(xml) {
  const out = []
  for (const p of xml.split(/<w:p[ >]/).slice(1)) {
    const text = [...p.matchAll(/<w:t\b[^>]*>([^<]*)<\/w:t>|<w:tab\/>/g)].map((m) => (m[1] === undefined ? ' ' : decode(m[1]))).join('')
    out.push(text)
  }
  return out
}

function splitBody(paras) {
  let idx = -1
  paras.forEach((t, i) => {
    if (/^\s*(references?|reference list|bibliography)\s*$/i.test(t)) idx = i
  })
  if (idx < 0) return { body: paras, refs: [] }
  const refs = []
  for (const t of paras.slice(idx + 1)) {
    if (/^\s*(appendix|table \d|figure \d)/i.test(t)) break
    if (t.trim()) refs.push(t.trim())
  }
  return { body: paras.slice(0, idx), refs }
}

// ---------- merging ----------
const norm = (s) =>
  (s || '')
    .normalize('NFD')
    .replace(/[̀-ͯ]/g, '')
    .toLowerCase()
    .replace(/[^a-z0-9]/g, '')
const doiOf = (it) => (it.DOI || '').toLowerCase().replace(/^https?:\/\/(dx\.)?doi\.org\//, '').trim()
const yearOf = (it) => String(it.issued?.['date-parts']?.[0]?.[0] ?? it.issued?.literal ?? 'n.d.')
const titleKey = (it) => norm(it.title).slice(0, 60) + '|' + yearOf(it)
const firstAuthor = (it) => {
  const a = (it.author || it.editor || [])[0]
  return a ? a.family || a.literal || '' : it.title || ''
}
const richness = (it) => Object.keys(it).length + (doiOf(it) ? 10 : 0)

function clean(it, idFor) {
  const c = { ...it }
  delete c.citationKey
  c.id = idFor
  return c
}

function mergeItems(tagged) {
  // tagged: [{item, docs:Set}]
  const groups = []
  const byDoi = new Map()
  const byTitle = new Map()
  const mergeAlias = new Map()
  for (const pair of overrides.merge || []) for (const k of pair.slice(1)) mergeAlias.set(k.toLowerCase(), pair[0].toLowerCase())
  for (const t of tagged) {
    let doi = doiOf(t.item)
    if (mergeAlias.has(doi)) doi = mergeAlias.get(doi)
    const tk = titleKey(t.item)
    let g = (doi && byDoi.get(doi)) || byTitle.get(tk)
    if (!g) {
      g = { items: [], docs: new Set() }
      groups.push(g)
    }
    g.items.push(t.item)
    for (const d of t.docs) g.docs.add(d)
    if (doi) byDoi.set(doi, g)
    byTitle.set(tk, g)
  }
  const excluded = new Set((overrides.exclude || []).map((s) => s.toLowerCase()))
  const out = []
  for (const g of groups) {
    const best = [...g.items].sort((a, b) => richness(b) - richness(a))[0]
    const doi = doiOf(best)
    const key = doi || titleKey(best)
    if (excluded.has(key)) continue
    let item = clean(best, 'ref-' + createHash('sha1').update(key).digest('hex').slice(0, 10))
    const fix = overrides.fix?.[key]
    if (fix) {
      for (const [k, v] of Object.entries(fix)) {
        if (v === null) delete item[k]
        else item[k] = v
      }
    }
    out.push({ item, docs: g.docs })
  }
  return out
}

// ---------- in-text citation check ----------
const surnameKey = norm
function citationsIn(body) {
  const text = body.join('\n')
  const found = new Map()
  const add = (authors, year, raw) => {
    const first = authors
      .replace(/^(e\.g\.,?|see also|see|cf\.|i\.e\.,?|for example,?|as cited in)\s+/i, '')
      .replace(/^([A-Z]\.\s*)+/, '')
      .split(/\s+et al\.?|\s*&\s*|\s+and\s+|,/)[0]
      .trim()
    if (!first || !/^[A-ZÀ-ɏ]/.test(first)) return
    const key = surnameKey(first) + '|' + year.slice(0, 4)
    if (!found.has(key)) found.set(key, raw.trim())
  }
  for (const m of text.matchAll(/\(([^()]*?\b(?:19|20)\d{2}[a-z]?[^()]*)\)/g)) {
    for (const part of m[1].split(';')) {
      const mm = part.trim().match(/^(.+?),\s*((?:19|20)\d{2}[a-z]?)(?:,\s*(?:19|20)\d{2}[a-z]?)*/)
      if (mm) {
        add(mm[1], mm[2], part)
        for (const y of part.slice(mm[1].length).matchAll(/(?:19|20)\d{2}/g)) add(mm[1], y[0], part)
      }
    }
  }
  for (const m of text.matchAll(/([A-Z][\p{L}'’\-]+(?:\s+(?:et al\.|and\s+[A-Z][\p{L}'’\-]+|&\s+[A-Z][\p{L}'’\-]+))?)\s+\(((?:19|20)\d{2})[a-z]?\)/gu)) {
    add(m[1], m[2], m[0])
  }
  return found
}

function entryKeys(item) {
  const keys = new Set()
  const y = yearOf(item) === 'n.d.' ? 'n.d.' : yearOf(item)
  const a = (item.author || item.editor || [])[0]
  const name = a ? [a['non-dropping-particle'], a.family].filter(Boolean).join(' ') || a.literal || '' : ''
  if (name) {
    keys.add(surnameKey(name) + '|' + y)
    keys.add(surnameKey(name.split(/\s+/).pop()) + '|' + y)
    const initials = name.split(/\s+/).filter((w) => /^[A-Z]/.test(w)).map((w) => w[0]).join('')
    if (initials.length > 1) keys.add(norm(initials) + '|' + y)
  }
  for (const alias of item._aliases || []) keys.add(surnameKey(alias) + '|' + y)
  return keys
}

function plainRefKey(line) {
  const m = line.match(/^(.+?)[,.]\s.*?\(?((?:19|20)\d{2}|n\.d\.)[a-z]?(?:, [A-Z][a-z]+(?: \d{1,2})?)?\)?[.:]/)
  return m ? surnameKey(m[1].trim()) + '|' + m[2] : null
}

// ---------- rendering ----------
const config = plugins.config.get('@csl')
config.templates.add('apa-local', readFileSync(join(here, 'styles/apa.csl'), 'utf8'))

function render(items) {
  const cite = new Cite(items.map(({ _aliases, ...rest }) => rest), { forceType: '@csl/list+object' })
  return cite.format('bibliography', { format: 'html', template: 'apa-local', lang: 'en-US', asEntryArray: true })
}

const htmlToText = (h) => decode(h.replace(/<[^>]+>/g, ''))
function htmlToMarkdown(h) {
  let s = h.replace(/<div class="csl-entry">|<\/div>/g, '').trim()
  const urls = []
  s = s.replace(/<a [^>]*href="([^"]+)"[^>]*>[^<]*<\/a>/g, (_, u) => `\u0000${urls.push(decode(u)) - 1}\u0000`)
  s = s.replace(/(https?:\/\/[^\s<]+[^\s<.,;)])/g, (u) => `\u0000${urls.push(decode(u)) - 1}\u0000`)
  s = s.replace(/<i>([\s\S]*?)<\/i>/g, '\u0001$1\u0001')
  s = decode(s.replace(/<[^>]+>/g, ''))
  s = s.replace(/([\\`*_[\]<>#|])/g, '\\$1')
  s = s.replace(/\u0001([\s\S]*?)\u0001/g, (_, t) => (t.trim() ? `*${t}*` : t))
  s = s.replace(/\u0000(\d+)\u0000/g, (_, i) => `<${urls[i]}>`)
  return s
}

const esc = (s) => s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;')
function linkify(html) {
  return html.replace(/(^|[\s>])(https?:\/\/[^\s<]+[^\s<.,;)])/g, (_, pre, u) => `${pre}<a href="${u}">${u}</a>`)
}

function longDate(d) {
  return d.toLocaleDateString('en-NZ', { day: 'numeric', month: 'long', year: 'numeric' })
}

// ---------- main ----------
const docs = sources.documents.map(pickDocument)
const tagged = []
const report = { docs: [], missingCitations: [], unmatchedPlain: [] }
const perDoc = []

for (const d of docs) {
  const xml = docxXml(d.path)
  const items = zoteroItems(xml)
  const { body, refs } = splitBody(paragraphs(xml))
  for (const it of items) tagged.push({ item: it, docs: new Set([d.label]) })
  perDoc.push({ d, body, refs, zotero: items.length })
}
for (const m of manual) tagged.push({ item: m, docs: new Set(m._citedIn || []) })
const merged = mergeItems(tagged.map((t) => ({ ...t, item: Object.fromEntries(Object.entries(t.item).filter(([k]) => k !== '_citedIn')) })))

const keyIndex = new Map()
for (const m of merged) for (const k of entryKeys(m.item)) keyIndex.set(k, m)

for (const { d, body, refs, zotero } of perDoc) {
  const cits = citationsIn(body)
  const missing = [...cits].filter(([k]) => !keyIndex.has(k)).map(([, raw]) => raw)
  const unmatchedPlain = refs.filter((r) => {
    const k = plainRefKey(r)
    return !k || !keyIndex.has(k)
  })
  report.docs.push(`- ${d.label}: ${d.file} (${zotero} Zotero citation items, ${cits.size} author-year citations found, ${refs.length} lines in its reference list)`)
  if (missing.length) report.missingCitations.push(`### ${d.label}\n` + missing.map((m) => `- ${m}`).join('\n'))
  if (unmatchedPlain.length) report.unmatchedPlain.push(`### ${d.label}\n` + unmatchedPlain.map((m) => `- ${m}`).join('\n'))
}

const entries = render(merged.map((m) => m.item))
const byId = new Map(merged.map((m) => [m.item.id, m]))
const csl = merged.map((m) => m.item).sort((a, b) => firstAuthor(a).localeCompare(firstAuthor(b)))

// keep the "last updated" date unless the list itself changed
const hash = createHash('sha1').update(JSON.stringify(entries)).digest('hex')
const prev = read('build-info.json', {})
const updated = prev.hash === hash && prev.updated ? prev.updated : new Date().toISOString().slice(0, 10)
const updatedLong = longDate(new Date(updated + 'T12:00:00'))
const builtFrom = docs.map((d) => `${d.label} (v${d.version})`).join(', ')

writeFileSync(join(here, 'references.json'), JSON.stringify(csl.map(({ _aliases, ...r }) => r), null, 1) + '\n')
writeFileSync(join(here, 'build-info.json'), JSON.stringify({ updated, hash, count: entries.length, builtFrom }, null, 1) + '\n')

const md = [
  '# Reference list',
  '',
  `APA 7th edition. ${entries.length} references. Last updated ${updatedLong}.`,
  '',
  `Built from the current drafts of: ${builtFrom}.`,
  '',
  'Web version with search: <https://charlotteprice-blip.github.io/phd-references/>. To import into Zotero, Mendeley or EndNote, download [references.json](references.json) (CSL JSON).',
  '',
  '---',
  '',
  ...entries.map(([, h]) => htmlToMarkdown(h) + '\n'),
].join('\n')
writeFileSync(join(here, 'README.md'), md)

const lis = entries
  .map(([id, h]) => {
    const inner = linkify(h.replace(/<div class="csl-entry">|<\/div>/g, '').trim())
    return `<li data-text="${esc(htmlToText(h).toLowerCase())}">${inner}</li>`
  })
  .join('\n')
writeFileSync(
  join(here, 'index.html'),
  readFileSync(join(here, 'template.html'), 'utf8')
    .replace('{{COUNT}}', String(entries.length))
    .replace('{{UPDATED}}', updatedLong)
    .replace('{{BUILT_FROM}}', esc(builtFrom))
    .replace('{{ENTRIES}}', lis),
)

const noDoi = merged
  .filter((m) => m.item.type === 'article-journal' && !doiOf(m.item))
  .map((m) => `- ${htmlToText(entries.find(([id]) => id === m.item.id)?.[1] || m.item.title)}`)
writeFileSync(
  join(here, 'check-report.md'),
  [
    `# Check report (${new Date().toISOString().slice(0, 16).replace('T', ' ')})`,
    '',
    '## Documents read',
    ...report.docs,
    '',
    '## In-text citations with no matching reference',
    report.missingCitations.join('\n\n') || 'None.',
    '',
    "## Lines in a document's own reference list with no matching reference",
    report.unmatchedPlain.join('\n\n') || 'None.',
    '',
    '## Journal articles with no DOI',
    noDoi.join('\n') || 'None.',
    '',
  ].join('\n'),
)

console.log(`${entries.length} references from ${builtFrom}`)
console.log(`missing citations: ${report.missingCitations.length ? 'see check-report.md' : 'none'}`)
