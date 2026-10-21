const express = require('express');
const path = require('path');
const os = require('os');
const fs = require('fs');
const dns = require('dns').promises;
const https = require('https');
const net = require('net');
const crypto = require('crypto');
const QRCode = require('qrcode');
const ical = require('node-ical');
require('dotenv').config();

const app = express();
const PORT = process.env.PORT || 3000;
const TODOS_FILE = path.join(__dirname, 'todos.json');
const CALENDAR_CONFIG_FILE = path.join(__dirname, '.calendar-source.json');
const AUSTRIAN_HOLIDAYS_URL = 'https://calendar.google.com/calendar/ical/de.austrian%23holiday%40group.v.calendar.google.com/public/basic.ics';
const CALENDAR_SOURCE_COLORS = ['amber', 'emerald', 'rose', 'blue', 'violet', 'cyan', 'orange', 'lime', 'pink', 'teal'];

function getLanAddresses() {
    return Object.entries(os.networkInterfaces()).flatMap(([name, addresses]) =>
        (addresses || []).filter(({ address, family, internal }) => {
            if (internal || (family !== 'IPv4' && family !== 4)) return false;
            const [first, second] = address.split('.').map(Number);
            return first === 10 || (first === 172 && second >= 16 && second <= 31) || (first === 192 && second === 168);
        }).map(({ address }) => ({ name, address }))
    );
}

app.use(express.json());
app.use(express.static(path.join(__dirname, 'public')));

// Hilfsfunktion: To-Dos laden
function getTodos() {
    if (!fs.existsSync(TODOS_FILE)) return [];
    try {
        return JSON.parse(fs.readFileSync(TODOS_FILE, 'utf8'));
    } catch (e) {
        return [];
    }
}

// Hilfsfunktion: To-Dos speichern
function saveTodos(todos) {
    fs.writeFileSync(TODOS_FILE, JSON.stringify(todos, null, 2), 'utf8');
}

function getCalendarConfig() {
    const defaults = { sources: [], showDefaultHolidays: true, quickEventPresets: null };
    if (!fs.existsSync(CALENDAR_CONFIG_FILE)) return defaults;
    try {
        const saved = JSON.parse(fs.readFileSync(CALENDAR_CONFIG_FILE, 'utf8'));
        if (Array.isArray(saved)) return { ...defaults, sources: saved };
        if (Array.isArray(saved.sources)) return {
            sources: saved.sources,
            showDefaultHolidays: saved.showDefaultHolidays !== false,
            quickEventPresets: Array.isArray(saved.quickEventPresets) ? normalizeQuickEventPresets(saved.quickEventPresets) : null
        };
        if (saved.url) return { ...defaults, sources: [{ id: 'calendar-legacy', name: 'iCloud-Kalender', url: saved.url }] };
        return defaults;
    } catch (e) {
        return defaults;
    }
}

function normalizeQuickEventPresets(presets) {
    if (!Array.isArray(presets)) return [];
    return presets.slice(0, 100).filter(preset =>
        preset && /^[a-z0-9_-]{1,80}$/i.test(String(preset.id || '')) && String(preset.title || '').trim()
    ).map(preset => ({
        id: String(preset.id),
        title: String(preset.title).trim().slice(0, 60),
        time: /^\d{2}:\d{2}$/.test(preset.time || '') ? preset.time : '',
        memberId: String(preset.memberId || '').slice(0, 80)
    }));
}

function getSavedCalendarSources() {
    const config = getCalendarConfig();
    const usedColors = new Set();
    const sources = config.sources.map(source => {
        const color = CALENDAR_SOURCE_COLORS.includes(source.color) && !usedColors.has(source.color)
            ? source.color
            : CALENDAR_SOURCE_COLORS.find(candidate => !usedColors.has(candidate));
        if (color) usedColors.add(color);
        return { ...source, color: color || source.color || 'amber' };
    });
    if (JSON.stringify(sources) !== JSON.stringify(config.sources)) {
        config.sources = sources;
        fs.writeFileSync(CALENDAR_CONFIG_FILE, JSON.stringify(config, null, 2), { encoding: 'utf8', mode: 0o600 });
    }
    return sources;
}

function saveCalendarSources(sources) {
    const config = getCalendarConfig();
    config.sources = sources;
    fs.writeFileSync(CALENDAR_CONFIG_FILE, JSON.stringify(config, null, 2), { encoding: 'utf8', mode: 0o600 });
}

function normalizeCalendarUrl(value) {
    const input = String(value || '').trim().replace(/^webcal:\/\//i, 'https://');
    let url;
    try {
        url = new URL(input);
    } catch (e) {
        return null;
    }
    const hostname = url.hostname.toLowerCase().replace(/^\[|\]$/g, '');
    if (url.protocol !== 'https:' || url.username || url.password || url.port || net.isIP(hostname) || hostname === 'localhost' || hostname.endsWith('.localhost') || hostname.endsWith('.local') || hostname.endsWith('.internal')) return null;
    return url.toString();
}

function isPublicAddress(address) {
    const family = net.isIP(address);
    if (family === 4) {
        const [first, second, third] = address.split('.').map(Number);
        const reserved = first === 0 || first === 10 || first === 127 ||
            (first === 169 && second === 254) ||
            (first === 172 && second >= 16 && second <= 31) ||
            (first === 192 && (second === 168 || (second === 0 && (third === 0 || third === 2)))) ||
            (first === 100 && second >= 64 && second <= 127) ||
            (first === 198 && ((second === 18 || second === 19) || (second === 51 && third === 100))) ||
            (first === 203 && second === 0 && third === 113) ||
            first >= 224;
        return !reserved;
    }
    if (family === 6) {
        const normalized = address.toLowerCase();
        if (normalized.startsWith('::ffff:')) {
            const mapped = normalized.slice(7);
            return net.isIP(mapped) === 4 && isPublicAddress(mapped);
        }
        const firstBlock = parseInt(normalized.split(':')[0] || '0', 16);
        return firstBlock >= 0x2000 && firstBlock <= 0x3fff && !normalized.startsWith('2001:db8:');
    }
    return false;
}

async function resolvePublicCalendarHost(hostname) {
    const addresses = await dns.lookup(hostname, { all: true, verbatim: true });
    if (!addresses.length || addresses.some(({ address }) => !isPublicAddress(address))) {
        throw new Error('Der Kalenderhost muss auf eine öffentliche IP-Adresse zeigen.');
    }
    return addresses[0];
}

async function downloadCalendar(urlString) {
    const url = new URL(urlString);
    const address = await resolvePublicCalendarHost(url.hostname);
    return new Promise((resolve, reject) => {
        const request = https.get(url, {
            timeout: 10000,
            lookup: (hostname, options, callback) => options.all
                ? callback(null, [address])
                : callback(null, address.address, address.family)
        }, response => {
            if (response.statusCode < 200 || response.statusCode >= 300) {
                response.resume();
                reject(new Error(response.statusCode >= 300 && response.statusCode < 400 ? 'Weiterleitungen für Kalenderlinks sind nicht erlaubt.' : `Kalender antwortet mit HTTP ${response.statusCode}.`));
                return;
            }
            let body = '';
            let size = 0;
            response.setEncoding('utf8');
            response.on('data', chunk => {
                size += Buffer.byteLength(chunk);
                if (size > 5 * 1024 * 1024) {
                    request.destroy(new Error('Kalenderdatei ist größer als 5 MB.'));
                    return;
                }
                body += chunk;
            });
            response.on('end', () => resolve(body));
            response.on('error', reject);
        });
        request.on('timeout', () => request.destroy(new Error('Zeitüberschreitung beim Kalenderabruf.')));
        request.on('error', reject);
    });
}

// API: To-Dos abrufen
app.get('/api/todos', (req, res) => {
    res.json(getTodos());
});

// API: Neues To-Do hinzufügen
app.post('/api/todos', (req, res) => {
    const { text } = req.body;
    if (!text || text.trim() === '') {
        return res.status(400).json({ error: 'Text darf nicht leer sein' });
    }

    const todos = getTodos();
    const newTodo = { id: Date.now(), text: text.trim(), completed: false };
    todos.push(newTodo);
    saveTodos(todos);

    res.json(newTodo);
});

// API: To-Do Status umschalten (Erledigt / Offen) oder löschen
app.delete('/api/todos/:id', (req, res) => {
    const id = Number(req.params.id);
    let todos = getTodos();
    todos = todos.filter(t => t.id !== id);
    saveTodos(todos);
    res.json({ success: true });
});

app.get('/api/calendar/sources', (req, res) => {
    res.json(getSavedCalendarSources().map(({ id, name, color }) => ({ id, name, color })));
});

app.get('/api/calendar/settings', (req, res) => {
    res.json({ showDefaultHolidays: getCalendarConfig().showDefaultHolidays });
});

app.get('/api/calendar/quick-actions', (req, res) => {
    const quickEventPresets = getCalendarConfig().quickEventPresets;
    res.json({ configured: Array.isArray(quickEventPresets), presets: quickEventPresets || [] });
});

app.put('/api/calendar/quick-actions', (req, res) => {
    if (!Array.isArray(req.body?.presets)) return res.status(400).json({ error: 'Ungültige Schnellaktionen.' });
    const config = getCalendarConfig();
    config.quickEventPresets = normalizeQuickEventPresets(req.body.presets);
    fs.writeFileSync(CALENDAR_CONFIG_FILE, JSON.stringify(config, null, 2), { encoding: 'utf8', mode: 0o600 });
    res.json({ configured: true, presets: config.quickEventPresets });
});

app.post('/api/calendar/settings', (req, res) => {
    const config = getCalendarConfig();
    config.showDefaultHolidays = req.body.showDefaultHolidays !== false;
    fs.writeFileSync(CALENDAR_CONFIG_FILE, JSON.stringify(config, null, 2), { encoding: 'utf8', mode: 0o600 });
    res.json({ showDefaultHolidays: config.showDefaultHolidays });
});

app.post('/api/calendar/sources', async (req, res) => {
    const name = String(req.body.name || '').trim().slice(0, 60);
    const url = normalizeCalendarUrl(req.body.url);
    const color = String(req.body.color || '');
    if (!name || !url) {
        return res.status(400).json({ error: 'Bitte einen Namen und eine gültige HTTPS- oder webcal-ICS-Adresse eintragen.' });
    }
    if (!CALENDAR_SOURCE_COLORS.includes(color)) return res.status(400).json({ error: 'Bitte eine gültige Kalenderfarbe auswählen.' });
    try {
        await resolvePublicCalendarHost(new URL(url).hostname);
        const sources = getSavedCalendarSources();
        if (sources.some(source => source.url === url)) return res.status(409).json({ error: 'Dieser Kalender ist bereits hinzugefügt.' });
        if (sources.some(source => source.color === color)) return res.status(409).json({ error: 'Diese Farbe wird bereits von einem anderen Kalender verwendet.' });
        const source = { id: crypto.randomUUID(), name, url, color };
        sources.push(source);
        saveCalendarSources(sources);
        res.json({ id: source.id, name: source.name, color: source.color });
    } catch (error) {
        res.status(400).json({ error: error.message || 'Der Kalenderhost konnte nicht sicher geprüft werden.' });
    }
});

app.put('/api/calendar/sources/:id', (req, res) => {
    const color = String(req.body.color || '');
    if (!CALENDAR_SOURCE_COLORS.includes(color)) return res.status(400).json({ error: 'Bitte eine gültige Kalenderfarbe auswählen.' });
    const sources = getSavedCalendarSources();
    const source = sources.find(item => item.id === req.params.id);
    if (!source) return res.status(404).json({ error: 'Kalender nicht gefunden.' });
    if (sources.some(item => item.id !== source.id && item.color === color)) {
        return res.status(409).json({ error: 'Diese Farbe wird bereits von einem anderen Kalender verwendet.' });
    }
    source.color = color;
    saveCalendarSources(sources);
    res.json({ id: source.id, name: source.name, color: source.color });
});

app.delete('/api/calendar/sources/:id', (req, res) => {
    const sources = getSavedCalendarSources();
    const remaining = sources.filter(source => source.id !== req.params.id);
    if (remaining.length === sources.length) return res.status(404).json({ error: 'Kalender nicht gefunden.' });
    saveCalendarSources(remaining);
    res.json({ success: true });
});

app.get('/api/calendar', async (req, res) => {
    const sources = getSavedCalendarSources();
    const defaultSources = getCalendarConfig().showDefaultHolidays ? [
        { id: 'default-holidays-de', name: 'Feiertage Deutschland', url: process.env.ICAL_URL },
        { id: 'default-holidays-at', name: 'Feiertage Österreich', url: AUSTRIAN_HOLIDAYS_URL }
    ] : [];
    for (const source of defaultSources) {
        const url = normalizeCalendarUrl(source.url);
        if (url && !sources.some(saved => saved.url === url)) sources.unshift({ ...source, url });
    }
    const upcomingEvents = [];
    const sourceErrors = [];
    const now = new Date();

    for (const source of sources) {
        try {
            const calendarText = await downloadCalendar(source.url);
            const events = await ical.async.parseICS(calendarText);
            for (const ev of Object.values(events)) {
                if (ev.type !== 'VEVENT' || new Date(ev.end) < now) continue;
                upcomingEvents.push({
                    id: `external-${source.id}-${ev.uid || upcomingEvents.length}`,
                    summary: ev.summary,
                    sourceName: source.name,
                    calendarColor: source.color || '',
                    description: typeof ev.description === 'string' ? ev.description : '',
                    location: typeof ev.location === 'string' ? ev.location : '',
                    start: ev.start,
                    end: ev.end,
                    date: new Date(ev.start).toISOString().slice(0, 10),
                    time: ev.datetype === 'date' ? '' : new Date(ev.start).toLocaleTimeString('de-DE', { hour: '2-digit', minute: '2-digit' }),
                    endTime: ev.datetype === 'date' ? '' : new Date(ev.end).toLocaleTimeString('de-DE', { hour: '2-digit', minute: '2-digit' })
                });
            }
        } catch (error) {
            sourceErrors.push(source.name);
        }
    }

    upcomingEvents.sort((a, b) => new Date(a.start) - new Date(b.start));
    res.json({ events: upcomingEvents.slice(0, 300), sourceErrors });
});

app.get('/api/status', (req, res) => {
    res.json({ status: 'online', message: 'Dashboard läuft!' });
});

app.get('/api/connection-info', (req, res) => {
    res.json({ addresses: getLanAddresses(), port: Number(PORT) });
});

app.get('/api/connection-qr', async (req, res) => {
    const address = String(req.query.address || '');
    if (!getLanAddresses().some(item => item.address === address)) {
        return res.status(400).json({ error: 'Diese Netzwerkadresse ist nicht verfügbar.' });
    }

    const url = `http://${address}:${PORT}/`;
    try {
        const qr = await QRCode.toDataURL(url, { width: 280, margin: 2, errorCorrectionLevel: 'M' });
        res.json({ url, qr });
    } catch (error) {
        res.status(500).json({ error: 'Der QR-Code konnte nicht erstellt werden.' });
    }
});

app.listen(PORT, () => {
    console.log(`🚀 Dashboard läuft lokal auf: http://localhost:${PORT}`);
});