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
const DASHBOARD_USER = process.env.DASHBOARD_USER || '';
const DASHBOARD_PASSWORD = process.env.DASHBOARD_PASSWORD || '';
const HOME_ASSISTANT_URL = process.env.HOME_ASSISTANT_URL || '';
const HOME_ASSISTANT_TOKEN = process.env.HOME_ASSISTANT_TOKEN || '';
const AUTH_SESSION_COOKIE = 'familien_dashboard_session';
const AUTH_SESSION_DURATION_MS = 12 * 60 * 60 * 1000;
const ORF_NOE_RSS_URL = 'https://rss.orf.at/noe.xml';
const LOCAL_UPDATES_CACHE_MS = 60 * 1000;
const ESPN_AUSTRIAN_BUNDESLIGA_URL = 'https://site.api.espn.com/apis/site/v2/sports/soccer/aut.1';
const ESPN_CHAMPIONS_LEAGUE_URL = 'https://site.api.espn.com/apis/site/v2/sports/soccer/uefa.champions';
const FOOTBALL_LEAGUES = [
    { url: ESPN_AUSTRIAN_BUNDESLIGA_URL, name: 'Österreichische Bundesliga' },
    { url: 'https://site.api.espn.com/apis/site/v2/sports/soccer/ger.1', name: 'Deutsche Bundesliga' },
    { url: ESPN_CHAMPIONS_LEAGUE_URL, name: 'Champions League' },
    { url: 'https://site.api.espn.com/apis/site/v2/sports/soccer/uefa.europa', name: 'Europa League' },
    { url: 'https://site.api.espn.com/apis/site/v2/sports/soccer/uefa.europa.conf', name: 'Conference League' }
];
const FOOTBALL_CACHE_MS = 60 * 1000;
const FOOTBALL_LIVE_CACHE_MS = 10 * 1000;
const FOOTBALL_LEAGUE_VIEWS = {
    'champions-league': { slug: 'uefa.champions', name: 'Champions League' },
    'bundesliga-at': { slug: 'aut.1', name: 'Österreichische Bundesliga' },
    'bundesliga-de': { slug: 'ger.1', name: 'Deutsche Bundesliga' },
    'la-liga': { slug: 'esp.1', name: 'La Liga' },
    'premier-league': { slug: 'eng.1', name: 'Premier League' }
};
const footballLeagueMatchesCache = new Map();
const footballStandingsCache = new Map();
const authSessions = new Map();
const loginAttempts = new Map();
let localUpdatesCache = { fetchedAt: 0, items: [] };
let localUpdatesRequest = null;
let footballTeamsCache = { fetchedAt: 0, teams: [] };
let footballTeamsRequest = null;
const footballMatchesCache = new Map();
const DATA_DIR = path.resolve(process.env.DATA_DIR || __dirname);
fs.mkdirSync(DATA_DIR, { recursive: true });
const TODOS_FILE = path.join(DATA_DIR, 'todos.json');
const CALENDAR_CONFIG_FILE = path.join(DATA_DIR, '.calendar-source.json');
const HOME_ASSISTANT_SELECTION_FILE = path.join(DATA_DIR, '.home-assistant-selection.json');
const HOME_ASSISTANT_WEATHER_FILE = path.join(DATA_DIR, '.home-assistant-weather.json');
const SHELLY_DEVICES_FILE = path.join(DATA_DIR, '.shelly-devices.json');
const AUSTRIAN_HOLIDAYS_URL = 'https://calendar.google.com/calendar/ical/de.austrian%23holiday%40group.v.calendar.google.com/public/basic.ics';
const CALENDAR_SOURCE_COLORS = ['amber', 'emerald', 'rose', 'blue', 'violet', 'cyan', 'orange', 'lime', 'pink', 'teal'];
const HOME_ASSISTANT_DOMAINS = ['light', 'switch', 'cover', 'fan', 'climate'];
const DEFAULT_HOME_ASSISTANT_CATEGORY = 'Allgemein';

if (process.env.NODE_ENV === 'production' && (!DASHBOARD_USER || !DASHBOARD_PASSWORD)) {
    throw new Error('DASHBOARD_USER und DASHBOARD_PASSWORD müssen im Produktionsbetrieb gesetzt sein.');
}

function constantTimeEqual(actual, expected) {
    const actualBuffer = Buffer.from(actual);
    const expectedBuffer = Buffer.from(expected);
    return actualBuffer.length === expectedBuffer.length && crypto.timingSafeEqual(actualBuffer, expectedBuffer);
}

function getSessionToken(req) {
    const prefix = `${AUTH_SESSION_COOKIE}=`;
    return (req.headers.cookie || '').split(';').map(cookie => cookie.trim()).find(cookie => cookie.startsWith(prefix))?.slice(prefix.length) || '';
}

function setSessionCookie(req, res, token) {
    const forwardedProtocol = (req.get('x-forwarded-proto') || '').split(',')[0].trim();
    const secure = req.secure || forwardedProtocol === 'https' ? '; Secure' : '';
    res.setHeader('Set-Cookie', `${AUTH_SESSION_COOKIE}=${token}; Path=/; HttpOnly; SameSite=Lax; Max-Age=${AUTH_SESSION_DURATION_MS / 1000}${secure}`);
}

function clearSessionCookie(req, res) {
    const forwardedProtocol = (req.get('x-forwarded-proto') || '').split(',')[0].trim();
    const secure = req.secure || forwardedProtocol === 'https' ? '; Secure' : '';
    res.setHeader('Set-Cookie', `${AUTH_SESSION_COOKIE}=; Path=/; HttpOnly; SameSite=Lax; Max-Age=0${secure}`);
}

function requireDashboardAuth(req, res, next) {
    if (!DASHBOARD_USER && !DASHBOARD_PASSWORD) return next();
    if (!DASHBOARD_USER || !DASHBOARD_PASSWORD) return res.status(503).send('Dashboard-Anmeldung ist nicht vollständig konfiguriert.');
    if (req.method === 'GET' && req.path === '/api/status') return next();

    const token = getSessionToken(req);
    const session = authSessions.get(token);
    if (session && session.expiresAt > Date.now()) return next();
    if (token) authSessions.delete(token);

    if (req.path.startsWith('/api/')) return res.status(401).json({ error: 'Anmeldung erforderlich.', loginRequired: true });
    const returnTo = req.originalUrl.startsWith('/') && !req.originalUrl.startsWith('//') ? req.originalUrl : '/';
    res.redirect(`/login?next=${encodeURIComponent(returnTo)}`);
}

function isLocalNetworkClient(address) {
    const normalized = String(address || '').toLowerCase();
    if (normalized === '::1') return true;
    const ipv4 = normalized.startsWith('::ffff:') ? normalized.slice(7) : normalized;
    if (net.isIP(ipv4) === 4) {
        const [first, second] = ipv4.split('.').map(Number);
        return first === 10 || first === 127 ||
            (first === 172 && second >= 16 && second <= 31) ||
            (first === 192 && second === 168);
    }
    return net.isIP(normalized) === 6 && /^(fc|fd|fe80:)/.test(normalized);
}

function getLanAddresses() {
    return Object.entries(os.networkInterfaces()).flatMap(([name, addresses]) =>
        (addresses || []).filter(({ address, family, internal }) => {
            if (internal || (family !== 'IPv4' && family !== 4)) return false;
            const [first, second] = address.split('.').map(Number);
            return first === 10 || (first === 172 && second >= 16 && second <= 31) || (first === 192 && second === 168);
        }).map(({ address }) => ({ name, address }))
    );
}

function getHomeAssistantBaseUrl() {
    try {
        const url = new URL(HOME_ASSISTANT_URL);
        if (!['http:', 'https:'].includes(url.protocol) || url.username || url.password || url.search || url.hash) return '';
        return url.toString().replace(/\/$/, '');
    } catch (error) {
        return '';
    }
}

function isSupportedHomeAssistantEntityId(entityId) {
    return typeof entityId === 'string' && new RegExp(`^(${HOME_ASSISTANT_DOMAINS.join('|')})\\.[a-z0-9_]+$`).test(entityId);
}

function getHomeAssistantDashboardConfig() {
    try {
        const saved = JSON.parse(fs.readFileSync(HOME_ASSISTANT_SELECTION_FILE, 'utf8'));
        const entityIds = [...new Set((Array.isArray(saved) ? saved : saved.entityIds || []).filter(isSupportedHomeAssistantEntityId))].slice(0, 80);
        const categories = [...new Set([DEFAULT_HOME_ASSISTANT_CATEGORY, ...(Array.isArray(saved.categories) ? saved.categories : [])
            .filter(category => typeof category === 'string')
            .map(category => category.trim().slice(0, 32))
            .filter(Boolean)])].slice(0, 30);
        const savedAssignments = Array.isArray(saved) ? {} : saved.entityCategories || {};
        const entityCategories = Object.fromEntries(entityIds.map(entityId => [
            entityId,
            categories.includes(savedAssignments[entityId]) ? savedAssignments[entityId] : DEFAULT_HOME_ASSISTANT_CATEGORY
        ]));
        return { entityIds, categories, entityCategories };
    } catch (error) {
        return { entityIds: [], categories: [DEFAULT_HOME_ASSISTANT_CATEGORY], entityCategories: {} };
    }
}

function saveHomeAssistantDashboardConfig(config) {
    fs.writeFileSync(HOME_ASSISTANT_SELECTION_FILE, JSON.stringify(config, null, 2), { encoding: 'utf8', mode: 0o600 });
}

async function requestHomeAssistant(pathname, options = {}) {
    const baseUrl = getHomeAssistantBaseUrl();
    if (!baseUrl || !HOME_ASSISTANT_TOKEN) throw new Error('Home Assistant ist noch nicht konfiguriert.');
    const url = new URL(pathname.replace(/^\//, ''), `${baseUrl}/`);
    const response = await fetch(url, {
        ...options,
        headers: {
            Authorization: `Bearer ${HOME_ASSISTANT_TOKEN}`,
            'Content-Type': 'application/json',
            ...options.headers
        },
        signal: AbortSignal.timeout(8000)
    });
    const result = await response.json().catch(() => null);
    if (!response.ok) throw new Error(result?.message || `Home Assistant antwortet mit HTTP ${response.status}.`);
    return result;
}

const HOME_ASSISTANT_WEATHER_FIELDS = ['temperature', 'humidity', 'pressure', 'wind', 'condition'];

function getHomeAssistantWeatherConfig() {
    const defaults = { enabled: false, stationName: 'Netatmo', entities: {} };
    try {
        const saved = JSON.parse(fs.readFileSync(HOME_ASSISTANT_WEATHER_FILE, 'utf8'));
        const entities = Object.fromEntries(HOME_ASSISTANT_WEATHER_FIELDS.map(field => [
            field,
            typeof saved.entities?.[field] === 'string' && /^sensor\.[a-z0-9_]+$/.test(saved.entities[field]) ? saved.entities[field] : ''
        ]));
        return {
            enabled: saved.enabled === true,
            stationName: String(saved.stationName || defaults.stationName).trim().slice(0, 40),
            entities
        };
    } catch (error) {
        return defaults;
    }
}

function classifyHomeAssistantWeatherSensor(entity) {
    const deviceClass = String(entity.attributes?.device_class || '').toLowerCase();
    const label = `${entity.entity_id} ${entity.attributes?.friendly_name || ''} ${deviceClass}`.toLowerCase();
    if (deviceClass === 'temperature' || /temperature|température|temperatur/.test(label)) return 'temperature';
    if (deviceClass === 'humidity' || /humidity|feuchtigkeit|luftfeuchte/.test(label)) return 'humidity';
    if (['pressure', 'atmospheric_pressure'].includes(deviceClass) || /pressure|luftdruck|barometer/.test(label)) return 'pressure';
    if (deviceClass === 'wind_speed' || /wind|böe|boee/.test(label)) return 'wind';
    if (deviceClass === 'precipitation' || /rain|regen|niederschlag/.test(label)) return 'condition';
    if (/condition|weather|wetterzustand/.test(label)) return 'condition';
    return '';
}

app.use(express.json({ limit: '2mb' }));

app.get('/login', (req, res) => {
    res.sendFile(path.join(__dirname, 'public', 'login.html'));
});

app.post('/api/auth/login', (req, res) => {
    if (!DASHBOARD_USER || !DASHBOARD_PASSWORD) {
        return res.status(503).json({ error: 'Die Anmeldung ist auf dem Server noch nicht konfiguriert.' });
    }

    const ip = req.ip || req.socket.remoteAddress || 'unknown';
    const now = Date.now();
    const attempts = loginAttempts.get(ip);
    const currentAttempts = attempts && attempts.resetAt > now ? attempts : { count: 0, resetAt: now + 15 * 60 * 1000 };
    if (currentAttempts.count >= 10) return res.status(429).json({ error: 'Zu viele Versuche. Bitte warte 15 Minuten.' });

    const username = String(req.body?.username || '');
    const password = String(req.body?.password || '');
    const validUser = constantTimeEqual(username, DASHBOARD_USER);
    const validPassword = constantTimeEqual(password, DASHBOARD_PASSWORD);
    if (!validUser || !validPassword) {
        currentAttempts.count++;
        loginAttempts.set(ip, currentAttempts);
        return res.status(401).json({ error: 'Benutzername oder Passwort ist falsch.' });
    }

    loginAttempts.delete(ip);
    const token = crypto.randomBytes(32).toString('hex');
    authSessions.set(token, { expiresAt: now + AUTH_SESSION_DURATION_MS });
    setSessionCookie(req, res, token);
    res.json({ success: true });
});

app.use((req, res, next) => {
    if (isLocalNetworkClient(req.socket.remoteAddress)) return next();
    res.status(403).send('Dieses Dashboard ist nur im lokalen Netzwerk erreichbar.');
});
app.use(requireDashboardAuth);
app.post('/api/auth/logout', (req, res) => {
    const token = getSessionToken(req);
    if (token) authSessions.delete(token);
    clearSessionCookie(req, res);
    res.json({ success: true });
});
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

function normalizeFeedText(value) {
    return String(value || '')
        .normalize('NFD')
        .replace(/[\u0300-\u036f]/g, '')
        .replace(/ß/g, 'ss')
        .toLowerCase()
        .replace(/[^a-z0-9]+/g, ' ')
        .trim();
}

function decodeFeedText(value) {
    return String(value || '')
        .replace(/<!\[CDATA\[([\s\S]*?)\]\]>/g, '$1')
        .replace(/<[^>]*>/g, ' ')
        .replace(/&(#x[0-9a-f]+|#\d+|amp|lt|gt|quot|apos|nbsp);/gi, (entity, code) => {
            if (code[0] !== '#') {
                return { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", nbsp: ' ' }[code.toLowerCase()] || entity;
            }
            const numeric = code[1].toLowerCase() === 'x'
                ? parseInt(code.slice(2), 16)
                : parseInt(code.slice(1), 10);
            return Number.isFinite(numeric) && numeric <= 0x10ffff ? String.fromCodePoint(numeric) : entity;
        })
        .replace(/\s+/g, ' ')
        .trim();
}

function getFeedTag(item, tagName) {
    const match = item.match(new RegExp(`<${tagName}\\b[^>]*>([\\s\\S]*?)<\\/${tagName}>`, 'i'));
    return match ? decodeFeedText(match[1]) : '';
}

function isGmuendDistrictFeedItem(text) {
    const normalized = ` ${normalizeFeedText(text)} `;
    const districtPlaces = [
        'Amaliendorf Aalfang', 'Bad Grosspertholz', 'Brand Nagelberg', 'Eggern', 'Eisgarn',
        'Gmund', 'Grossdietmanns', 'Grossschonau', 'Haugschlag', 'Heidenreichstein',
        'Hirschbach', 'Hoheneich', 'Kirchberg am Walde', 'Litschau', 'Moorbad Harbach',
        'Reingers', 'Schrems', 'St Martin', 'Unserfrau Altweitra', 'Waldenstein', 'Weitra'
    ];
    return districtPlaces.some(place => normalized.includes(` ${normalizeFeedText(place)} `));
}

function parseOrfNoeFeed(xml) {
    const trafficPattern = /\b(verkehr|stau|unfall|strassensperre|strassensperrung|umleitung|baustelle|fahrbahn|strasse gesperrt)\b/i;
    return [...xml.matchAll(/<item\b[^>]*>([\s\S]*?)<\/item>/gi)]
        .map(([ , item]) => {
            const title = getFeedTag(item, 'title');
            const description = getFeedTag(item, 'description');
            const link = getFeedTag(item, 'link');
            const publishedAt = getFeedTag(item, 'pubDate');
            let url = '';
            try {
                const parsed = new URL(link);
                if (parsed.protocol === 'https:' && (parsed.hostname === 'orf.at' || parsed.hostname.endsWith('.orf.at'))) {
                    url = parsed.toString();
                }
            } catch (error) {}
            return { title, description, url, publishedAt };
        })
        .filter(item => item.title && item.url && isGmuendDistrictFeedItem(`${item.title} ${item.description}`))
        .slice(0, 20)
        .map(item => ({
            ...item,
            description: item.description.slice(0, 280),
            type: trafficPattern.test(normalizeFeedText(`${item.title} ${item.description}`)) ? 'traffic' : 'news'
        }));
}

async function fetchOrfNoeUpdates() {
    const response = await fetch(ORF_NOE_RSS_URL, {
        headers: { Accept: 'application/rss+xml, application/xml, text/xml' },
        redirect: 'error',
        signal: AbortSignal.timeout(10000)
    });
    if (!response.ok) throw new Error(`ORF Niederösterreich antwortet mit HTTP ${response.status}.`);
    const xml = await response.text();
    if (Buffer.byteLength(xml, 'utf8') > 2 * 1024 * 1024) throw new Error('Der ORF-NÖ-Nachrichtenfeed ist unerwartet groß.');
    if (!/<rss\b|<rdf:RDF\b/i.test(xml)) throw new Error('ORF Niederösterreich hat kein gültiges RSS-Format geliefert.');
    return parseOrfNoeFeed(xml);
}

// WLAN-Name des Servers (Browser dürfen den Netzwerknamen nicht auslesen)
const { execFile } = require('child_process');
let networkNameCache = { name: '', at: 0 };

function runQuick(command, args) {
    return new Promise(resolve => {
        execFile(command, args, { timeout: 3000 }, (error, stdout) => resolve(error ? '' : String(stdout).trim()));
    });
}

async function detectNetworkName() {
    let name = '';
    if (process.platform === 'darwin') {
        const hardwarePorts = await runQuick('networksetup', ['-listallhardwareports']);
        let hardwarePort = '';
        const wifiDevices = [];
        for (const line of hardwarePorts.split('\n')) {
            const portMatch = line.match(/^Hardware Port:\s*(.+)$/i);
            const deviceMatch = line.match(/^Device:\s*(\S+)$/i);
            if (portMatch) hardwarePort = portMatch[1];
            else if (deviceMatch && /wi-?fi|airport/i.test(hardwarePort)) wifiDevices.push(deviceMatch[1]);
        }
        for (const device of wifiDevices) {
            const out = await runQuick('networksetup', ['-getairportnetwork', device]);
            const match = out.match(/Current Wi-Fi Network:\s*(.+)$/im);
            if (match) {
                name = match[1].trim();
                break;
            }
        }
    } else if (process.platform === 'linux') {
        name = await runQuick('iwgetid', ['-r']);
        if (!name) {
            const devices = await runQuick('iw', ['dev']);
            const interfaces = [...devices.matchAll(/^\s*Interface\s+(\S+)/gm)].map(match => match[1]);
            for (const device of interfaces) {
                const out = await runQuick('iw', ['dev', device, 'link']);
                const match = out.match(/^\s*SSID:\s*(.+)$/m);
                if (match) {
                    name = match[1].trim();
                    break;
                }
            }
        }
        if (!name) {
            const out = await runQuick('nmcli', ['-t', '--escape', 'no', '-f', 'IN-USE,SSID', 'dev', 'wifi']);
            const line = out.split('\n').find(entry => entry.startsWith('*:') || entry.startsWith('yes:'));
            name = line ? line.slice(line.indexOf(':') + 1).trim() : '';
        }
    }
    return name && !/redacted/i.test(name) ? name.slice(0, 60) : '';
}

app.get('/api/network-name', async (req, res) => {
    if (Date.now() - networkNameCache.at > 60000) {
        networkNameCache = { name: await detectNetworkName(), at: Date.now() };
    }
    const addresses = Object.values(require('os').networkInterfaces()).flat().filter(item => item && item.family === 'IPv4' && !item.internal);
    res.set('Cache-Control', 'no-store').json({ name: networkNameCache.name, ip: addresses[0]?.address || '' });
});

// Feuerwehr-Einsätze (Bezirk Gmünd) aus dem öffentlichen NÖ-Wastl-Feed der FF Krems
const FIRE_DISTRICT = '05';
const FIRE_FEED_URL = `https://www.feuerwehr-krems.at/CodePages/Wastl/GetDaten/GetWastlBezirkS3.asp?bezirk=${FIRE_DISTRICT}`;
const FIRE_POLL_MS = 15000;
const FIRE_MAX_HISTORY = 50;
const fireState = { stations: new Map(), baseline: false, history: [], summary: null, updatedAt: null, error: null, lastFetch: 0, pending: null };

function xmlValue(block, tag) {
    const match = block.match(new RegExp(`<${tag}>\\s*(?:<!\\[CDATA\\[([\\s\\S]*?)\\]\\]>|([\\s\\S]*?))\\s*</${tag}>`));
    return match ? (match[1] ?? match[2] ?? '') : '';
}

function parseFireFeed(xml) {
    const stations = [...xml.matchAll(/<aFFNr[^>]*>([\s\S]*?)<\/aFFNr>/g)].map(match => {
        const block = match[1];
        const button = xmlValue(block, 'Button').toLowerCase();
        const lines = xmlValue(block, 'Title').split(/\r?\n/).map(line => line.trim()).filter(Boolean);
        const status = button.includes('red') ? 'red' : button.includes('orange') || button.includes('yellow') ? 'orange' : button.includes('green') ? 'green' : 'other';
        const first = (lines[0] || '').replace(/\s+einsatzbereit!?$/i, '');
        return {
            id: xmlValue(block, 'FFNr').trim(),
            name: first || `FF ${xmlValue(block, 'FFNr').trim()}`,
            status,
            info: status === 'green' ? [] : lines.slice(1)
        };
    }).filter(station => station.id);
    const bazBlock = [...xml.matchAll(/<aBAZID[^>]*>([\s\S]*?)<\/aBAZID>/g)].map(match => match[1]).find(block => xmlValue(block, 'cBezirk').trim() === FIRE_DISTRICT);
    const summary = bazBlock ? {
        name: xmlValue(bazBlock, 'cFriendlyName').trim(),
        stationCount: Number.parseInt(xmlValue(bazBlock, 'CountFeuerwehr'), 10) || 0,
        incidentCount: Number.parseInt(xmlValue(bazBlock, 'CountEinsatz'), 10) || 0,
        level: Number.parseInt(xmlValue(bazBlock, 'nStufe'), 10) || 0
    } : null;
    return { stations, summary };
}

async function refreshFireData() {
    const response = await fetch(FIRE_FEED_URL, { headers: { 'User-Agent': 'Mozilla/5.0 Familien-Dashboard' }, signal: AbortSignal.timeout(10000) });
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    const { stations, summary } = parseFireFeed(await response.text());
    if (!stations.length) throw new Error('Keine Feuerwehr-Daten gefunden.');
    const now = new Date().toISOString();
    const next = new Map();
    for (const station of stations) {
        const previous = fireState.stations.get(station.id);
        const startedAt = station.status === 'red' ? (previous?.status === 'red' ? previous.startedAt : now) : null;
        next.set(station.id, { ...station, startedAt });
        if (fireState.baseline && station.status === 'red' && previous && previous.status !== 'red') {
            fireState.history.unshift({ id: `${station.id}-${Date.now()}`, stationId: station.id, name: station.name, info: station.info, startedAt: now });
            fireState.history.length = Math.min(fireState.history.length, FIRE_MAX_HISTORY);
        }
    }
    fireState.stations = next;
    fireState.baseline = true;
    fireState.summary = summary;
    fireState.updatedAt = now;
    fireState.error = null;
}

function ensureFireData() {
    if (fireState.pending) return fireState.pending;
    if (Date.now() - fireState.lastFetch < 5000) return Promise.resolve();
    fireState.lastFetch = Date.now();
    fireState.pending = refreshFireData()
        .catch(error => { fireState.error = error.message; })
        .finally(() => { fireState.pending = null; });
    return fireState.pending;
}

setInterval(ensureFireData, FIRE_POLL_MS).unref();
ensureFireData();

app.get('/api/fire', async (req, res) => {
    await ensureFireData();
    if (!fireState.updatedAt) return res.status(502).json({ error: 'Feuerwehr-Daten sind gerade nicht erreichbar.' });
    const stations = [...fireState.stations.values()];
    const active = stations.filter(station => station.status === 'red').map(({ id, name, info, startedAt }) => ({ id, name, info, startedAt }));
    const alerted = stations.filter(station => station.status === 'orange').map(({ id, name, info }) => ({ id, name, info }));
    res.set('Cache-Control', 'no-store').json({
        district: fireState.summary?.name || 'BAZ Gmünd',
        stationCount: stations.length,
        activeCount: active.length,
        active,
        alerted,
        incidentCount: fireState.summary?.incidentCount ?? active.length,
        history: fireState.history,
        updatedAt: fireState.updatedAt,
        stale: Boolean(fireState.error)
    });
});

app.get('/api/local-updates', async (req, res) => {
    if (Date.now() - localUpdatesCache.fetchedAt < LOCAL_UPDATES_CACHE_MS) {
        return res.json({ items: localUpdatesCache.items, updatedAt: new Date(localUpdatesCache.fetchedAt).toISOString() });
    }

    try {
        localUpdatesRequest ||= fetchOrfNoeUpdates();
        const items = await localUpdatesRequest;
        localUpdatesCache = { fetchedAt: Date.now(), items };
        res.json({ items, updatedAt: new Date(localUpdatesCache.fetchedAt).toISOString() });
    } catch (error) {
        res.status(502).json({ error: error.message || 'Der ORF-NÖ-Nachrichtenfeed konnte nicht geladen werden.' });
    } finally {
        localUpdatesRequest = null;
    }
});

async function fetchEspnJson(url) {
    const response = await fetch(url, {
        headers: { Accept: 'application/json' },
        redirect: 'error',
        signal: AbortSignal.timeout(10000)
    });
    if (!response.ok) throw new Error(`Der Live-Spielstand-Dienst antwortet mit HTTP ${response.status}.`);
    const body = await response.text();
    if (Buffer.byteLength(body, 'utf8') > 3 * 1024 * 1024) throw new Error('Die Live-Spielstand-Antwort ist unerwartet groß.');
    try {
        return JSON.parse(body);
    } catch (error) {
        throw new Error('Der Live-Spielstand-Dienst hat ungültige Daten geliefert.');
    }
}

async function fetchLeagueTeams(league) {
    const url = new URL(`${league.url}/teams`);
    url.searchParams.set('limit', '100');
    const data = await fetchEspnJson(url);
    return (data.sports || []).flatMap(sport =>
        (sport.leagues || []).flatMap(item => (item.teams || []).map(({ team }) => ({
            id: String(team.id || ''),
            name: String(team.displayName || team.name || '').slice(0, 80),
            shortName: String(team.shortDisplayName || team.abbreviation || team.displayName || '').slice(0, 40),
            leagues: [league.name]
        })))
    ).filter(team => /^\d{1,12}$/.test(team.id) && team.name);
}

async function getAustrianBundesligaTeams() {
    if (Date.now() - footballTeamsCache.fetchedAt < 24 * 60 * 60 * 1000) return footballTeamsCache.teams;
    footballTeamsRequest ||= (async () => {
        const results = await Promise.allSettled(FOOTBALL_LEAGUES.map(fetchLeagueTeams));
        if (results[0].status !== 'fulfilled' || !results[0].value.length) {
            throw new Error('Die Fußballvereine konnten nicht geladen werden.');
        }
        const byId = new Map();
        for (const result of results) {
            if (result.status !== 'fulfilled') continue;
            for (const team of result.value) {
                const existing = byId.get(team.id);
                if (existing) existing.leagues = [...new Set([...existing.leagues, ...team.leagues])];
                else byId.set(team.id, team);
            }
        }
        const teams = [...byId.values()].sort((a, b) => a.name.localeCompare(b.name, 'de')).slice(0, 300);
        footballTeamsCache = { fetchedAt: Date.now(), teams };
        return teams;
    })();
    try {
        return await footballTeamsRequest;
    } finally {
        footballTeamsRequest = null;
    }
}

function getViennaDateKey(date = new Date()) {
    const parts = new Intl.DateTimeFormat('en-CA', {
        timeZone: 'Europe/Vienna',
        year: 'numeric',
        month: '2-digit',
        day: '2-digit'
    }).formatToParts(date);
    const values = Object.fromEntries(parts.map(part => [part.type, part.value]));
    return `${values.year}${values.month}${values.day}`;
}

function addDaysToDateKey(dateKey, days) {
    const date = new Date(Date.UTC(Number(dateKey.slice(0, 4)), Number(dateKey.slice(4, 6)) - 1, Number(dateKey.slice(6, 8)) + days));
    return `${date.getUTCFullYear()}${String(date.getUTCMonth() + 1).padStart(2, '0')}${String(date.getUTCDate()).padStart(2, '0')}`;
}

function mapEspnFootballEvent(event, leagueName = '') {
    const competition = event.competitions?.[0];
    const status = competition?.status;
    const competitors = competition?.competitors || [];
    const home = competitors.find(team => team.homeAway === 'home');
    const away = competitors.find(team => team.homeAway === 'away');
    if (!competition || !home?.team?.id || !away?.team?.id) return null;
    return {
        id: String(event.id || ''),
        league: leagueName,
        startTime: String(event.date || competition.date || ''),
        name: String(event.name || ''),
        status: {
            state: String(status?.type?.state || 'pre'),
            detail: String(status?.type?.shortDetail || status?.type?.detail || ''),
            clock: String(status?.displayClock || '')
        },
        home: {
            id: String(home.team.id),
            name: String(home.team.displayName || home.team.name || ''),
            score: String(home.score ?? '0')
        },
        away: {
            id: String(away.team.id),
            name: String(away.team.displayName || away.team.name || ''),
            score: String(away.score ?? '0')
        }
    };
}

app.get('/api/football/teams', async (req, res) => {
    try {
        res.json({ teams: await getAustrianBundesligaTeams() });
    } catch (error) {
        res.status(502).json({ error: error.message || 'Die Fußballvereine konnten nicht geladen werden.' });
    }
});

app.get('/api/football/matches', async (req, res) => {
    const selectedIds = [...new Set(String(req.query.teams || '').split(',').filter(Boolean))].slice(0, 12);
    if (!selectedIds.length || selectedIds.some(id => !/^\d{1,12}$/.test(id))) {
        return res.status(400).json({ error: 'Bitte wähle mindestens einen gültigen Fußballverein aus.' });
    }

    try {
        const teams = await getAustrianBundesligaTeams();
        const validIds = new Set(teams.map(team => team.id));
        if (selectedIds.some(id => !validIds.has(id))) {
            return res.status(400).json({ error: 'Die Auswahl enthält einen unbekannten Fußballverein.' });
        }

        const from = getViennaDateKey();
        const to = addDaysToDateKey(from, 1);
        const selectedKey = selectedIds.sort().join(',');
        const cacheKey = `${from}:${to}:${selectedKey}`;
        const cached = footballMatchesCache.get(cacheKey);
        if (cached && Date.now() - cached.fetchedAt < (cached.matches.some(match => match.status.state === 'in') ? FOOTBALL_LIVE_CACHE_MS : FOOTBALL_CACHE_MS)) {
            return res.json({ matches: cached.matches, updatedAt: new Date(cached.fetchedAt).toISOString() });
        }

        const requests = FOOTBALL_LEAGUES.flatMap(league => [from, to].map(async date => {
            const url = new URL(`${league.url}/scoreboard`);
            url.searchParams.set('dates', date);
            url.searchParams.set('limit', '100');
            return { league, data: await fetchEspnJson(url) };
        }));
        const settled = await Promise.allSettled(requests);
        if (settled.every(item => item.status === 'rejected')) throw settled[0].reason;
        const selected = new Set(selectedIds);
        const seen = new Set();
        const matches = settled.filter(item => item.status === 'fulfilled')
            .flatMap(({ value }) => (value.data.events || []).map(event => mapEspnFootballEvent(event, value.league.name)))
            .filter(match => match && !seen.has(match.id) && seen.add(match.id))
            .filter(match => match && (selected.has(match.home.id) || selected.has(match.away.id)))
            .sort((first, second) => first.startTime.localeCompare(second.startTime))
            .slice(0, 30);
        const fetchedAt = Date.now();
        footballMatchesCache.set(cacheKey, { fetchedAt, matches });
        for (const [key, value] of footballMatchesCache) {
            if (Date.now() - value.fetchedAt > 5 * FOOTBALL_CACHE_MS) footballMatchesCache.delete(key);
        }
        res.json({ matches, updatedAt: new Date(fetchedAt).toISOString() });
    } catch (error) {
        res.status(502).json({ error: error.message || 'Live-Spiele konnten nicht geladen werden.' });
    }
});

function getFootballLeagueView(req, res) {
    const view = Object.hasOwn(FOOTBALL_LEAGUE_VIEWS, req.params.league) ? FOOTBALL_LEAGUE_VIEWS[req.params.league] : null;
    if (!view) res.status(404).json({ error: 'Unbekannter Wettbewerb.' });
    return view;
}

function getFootballMonthKeys() {
    const today = getViennaDateKey();
    const year = Number(today.slice(0, 4));
    const month = Number(today.slice(4, 6));
    const offsets = Number(today.slice(6, 8)) <= 10 ? [-1, 0, 1, 2] : [0, 1, 2];
    return offsets.map(offset => {
        const date = new Date(Date.UTC(year, month - 1 + offset, 1));
        return `${date.getUTCFullYear()}${String(date.getUTCMonth() + 1).padStart(2, '0')}`;
    });
}

app.get('/api/football/league/:league/matches', async (req, res) => {
    const view = getFootballLeagueView(req, res);
    if (!view) return;
    try {
        const cached = footballLeagueMatchesCache.get(req.params.league);
        const ttl = cached?.matches.some(match => match.status.state === 'in') ? FOOTBALL_LIVE_CACHE_MS : 5 * 60 * 1000;
        if (cached && Date.now() - cached.fetchedAt < ttl) {
            return res.json({ matches: cached.matches, updatedAt: new Date(cached.fetchedAt).toISOString() });
        }
        const settled = await Promise.allSettled(getFootballMonthKeys().map(month => {
            const url = new URL(`https://site.api.espn.com/apis/site/v2/sports/soccer/${view.slug}/scoreboard`);
            url.searchParams.set('dates', month);
            url.searchParams.set('limit', '1000');
            return fetchEspnJson(url);
        }));
        if (settled.every(item => item.status === 'rejected')) throw settled[0].reason;
        const seen = new Set();
        const matches = settled.filter(item => item.status === 'fulfilled')
            .flatMap(item => item.value.events || [])
            .map(event => mapEspnFootballEvent(event, view.name))
            .filter(match => match && !seen.has(match.id) && seen.add(match.id))
            .sort((first, second) => first.startTime.localeCompare(second.startTime))
            .slice(0, 500);
        const fetchedAt = Date.now();
        footballLeagueMatchesCache.set(req.params.league, { fetchedAt, matches });
        res.json({ matches, updatedAt: new Date(fetchedAt).toISOString() });
    } catch (error) {
        res.status(502).json({ error: error.message || 'Spiele konnten nicht geladen werden.' });
    }
});

app.get('/api/football/league/:league/standings', async (req, res) => {
    const view = getFootballLeagueView(req, res);
    if (!view) return;
    try {
        const cached = footballStandingsCache.get(req.params.league);
        if (cached && Date.now() - cached.fetchedAt < 5 * 60 * 1000) {
            return res.json({ groups: cached.groups, updatedAt: new Date(cached.fetchedAt).toISOString() });
        }
        const data = await fetchEspnJson(new URL(`https://site.api.espn.com/apis/v2/sports/soccer/${view.slug}/standings`));
        const groups = (data.children || [data]).map(group => ({
            name: String(group.name || ''),
            entries: (group.standings?.entries || []).map(entry => {
                const stats = Object.fromEntries((entry.stats || []).map(stat => [stat.name, stat.displayValue ?? stat.value]));
                return {
                    rank: Number(stats.rank) || 0,
                    team: {
                        id: String(entry.team?.id || ''),
                        name: String(entry.team?.displayName || entry.team?.name || '')
                    },
                    played: String(stats.gamesPlayed ?? ''),
                    wins: String(stats.wins ?? ''),
                    draws: String(stats.ties ?? ''),
                    losses: String(stats.losses ?? ''),
                    goalsFor: String(stats.pointsFor ?? ''),
                    goalsAgainst: String(stats.pointsAgainst ?? ''),
                    goalDifference: String(stats.pointDifferential ?? ''),
                    points: String(stats.points ?? ''),
                    note: String(entry.note?.description || ''),
                    noteColor: /^#[0-9a-f]{3,8}$/i.test(entry.note?.color || '') ? entry.note.color : ''
                };
            }).filter(entry => /^\d{1,12}$/.test(entry.team.id)).sort((first, second) => first.rank - second.rank)
        })).filter(group => group.entries.length);
        if (!groups.length) throw new Error('Für diesen Wettbewerb ist noch keine Tabelle verfügbar.');
        const fetchedAt = Date.now();
        footballStandingsCache.set(req.params.league, { fetchedAt, groups });
        res.json({ groups, updatedAt: new Date(fetchedAt).toISOString() });
    } catch (error) {
        res.status(502).json({ error: error.message || 'Die Tabelle konnte nicht geladen werden.' });
    }
});

// Kameras: Live-Bild, Standbilder und Bewegungsaufnahmen
const CAMERAS_FILE = path.join(DATA_DIR, '.cameras.json');
const CAMERA_EVENTS_DIR = path.join(DATA_DIR, 'camera-events');
const MAX_CAMERAS = 12;
const MAX_CAMERA_EVENTS = 30;
const MAX_CAMERA_IMAGE_BYTES = 6 * 1024 * 1024;
const MAX_CAMERA_STREAMS = 4;
const CAMERA_MOTION_POLL_MS = 3000;
const CAMERA_MOTION_COOLDOWN_MS = 10 * 1000;
const CAMERA_EVENT_FILE_PATTERN = /^[a-f0-9]{8}-\d{13}\.(jpg|png)$/;
const FFMPEG_PATH = process.env.FFMPEG_PATH || 'ffmpeg';
const cameraMotionState = new Map();
const cameraLastCapture = new Map();
let activeCameraStreams = 0;
let cameraMotionPolling = false;

function isLocalCameraHost(hostname) {
    const host = hostname.replace(/^\[|\]$/g, '').toLowerCase();
    if (host === 'localhost' || host.endsWith('.local') || host.endsWith('.lan') || host.endsWith('.home') || !host.includes('.') && !host.includes(':')) return true;
    if (/^\d{1,3}(\.\d{1,3}){3}$/.test(host)) {
        const [first, second] = host.split('.').map(Number);
        return first === 10 || first === 127 || (first === 172 && second >= 16 && second <= 31) || (first === 192 && second === 168) || (first === 169 && second === 254);
    }
    return host === '::1' || /^f[cd][0-9a-f]{2}:/.test(host) || /^fe80:/.test(host);
}

function parseCameraUrl(value) {
    if (typeof value !== 'string' || !value.trim()) return '';
    let url;
    try {
        url = new URL(value.trim());
    } catch (error) {
        throw new Error('Die Kameraadresse ist ungültig.');
    }
    if (!['http:', 'https:'].includes(url.protocol) || url.hash) throw new Error('Kameraadressen müssen mit http:// oder https:// beginnen.');
    if (!isLocalCameraHost(url.hostname)) throw new Error('Kameras müssen im lokalen Netzwerk erreichbar sein (z. B. 192.168.x.x).');
    return url.toString().slice(0, 600);
}

function parseRtspUrl(value) {
    if (typeof value !== 'string' || !value.trim()) throw new Error('Bitte gib die RTSP-Adresse der Kamera ein.');
    let url;
    try {
        url = new URL(value.trim());
    } catch (error) {
        throw new Error('Die RTSP-Adresse ist ungültig.');
    }
    if (!['rtsp:', 'rtsps:'].includes(url.protocol) || url.hash) throw new Error('RTSP-Adressen müssen mit rtsp:// beginnen.');
    if (!isLocalCameraHost(url.hostname)) throw new Error('Kameras müssen im lokalen Netzwerk erreichbar sein (z. B. 192.168.x.x).');
    return value.trim().slice(0, 600);
}

function ffmpegRtspArgs(rtspUrl, outputArgs) {
    return ['-hide_banner', '-loglevel', 'error', '-rtsp_transport', 'tcp', '-timeout', '8000000', '-i', rtspUrl, '-an', ...outputArgs, 'pipe:1'];
}

function ffmpegMissingMessage(error) {
    return error.code === 'ENOENT'
        ? 'ffmpeg ist auf dem Server nicht installiert (Raspberry Pi: sudo apt install ffmpeg).'
        : 'Der Kamera-Stream konnte nicht gelesen werden.';
}

function grabRtspSnapshot(rtspUrl) {
    return new Promise((resolve, reject) => {
        const { spawn } = require('child_process');
        const child = spawn(FFMPEG_PATH, ffmpegRtspArgs(rtspUrl, ['-frames:v', '1', '-q:v', '4', '-f', 'image2pipe', '-vcodec', 'mjpeg']), { stdio: ['ignore', 'pipe', 'ignore'] });
        const chunks = [];
        let size = 0;
        const timer = setTimeout(() => child.kill('SIGKILL'), 12000);
        child.stdout.on('data', chunk => {
            size += chunk.length;
            if (size > MAX_CAMERA_IMAGE_BYTES) child.kill('SIGKILL');
            else chunks.push(chunk);
        });
        child.on('error', error => {
            clearTimeout(timer);
            reject(new Error(ffmpegMissingMessage(error)));
        });
        child.on('close', () => {
            clearTimeout(timer);
            const buffer = Buffer.concat(chunks);
            if (buffer.length > 100 && size <= MAX_CAMERA_IMAGE_BYTES) resolve(buffer);
            else reject(new Error('Von der Kamera kam kein Bild. Prüfe Adresse, Benutzername und Passwort.'));
        });
    });
}

function getCameras() {
    try {
        const saved = JSON.parse(fs.readFileSync(CAMERAS_FILE, 'utf8'));
        return (Array.isArray(saved) ? saved : []).filter(camera =>
            camera && /^[a-f0-9]{8}$/.test(camera.id) && typeof camera.name === 'string' && ['home-assistant', 'url', 'rtsp'].includes(camera.type)
        ).slice(0, MAX_CAMERAS);
    } catch (error) {
        return [];
    }
}

function saveCameras(cameras) {
    fs.writeFileSync(CAMERAS_FILE, JSON.stringify(cameras, null, 2), { encoding: 'utf8', mode: 0o600 });
}

function publicCamera(camera) {
    let address = '';
    if (camera.type === 'url' || camera.type === 'rtsp') {
        try { address = new URL(camera.snapshotUrl || camera.rtspUrl).host; } catch (error) { address = ''; }
    }
    return {
        id: camera.id,
        name: camera.name,
        type: camera.type,
        entityId: camera.entityId || '',
        motionEntityId: camera.motionEntityId || '',
        address,
        hasStream: camera.type !== 'url' || Boolean(camera.streamUrl)
    };
}

function cameraRequestTarget(rawUrl) {
    const url = new URL(rawUrl);
    const headers = {};
    if (url.username || url.password) {
        headers.Authorization = `Basic ${Buffer.from(`${decodeURIComponent(url.username)}:${decodeURIComponent(url.password)}`).toString('base64')}`;
        url.username = '';
        url.password = '';
    }
    return { url, headers };
}

function fetchCameraSource(camera, kind, signal) {
    if (camera.type === 'home-assistant') {
        const baseUrl = getHomeAssistantBaseUrl();
        if (!baseUrl || !HOME_ASSISTANT_TOKEN) throw new Error('Home Assistant ist noch nicht konfiguriert.');
        const endpoint = kind === 'stream' ? 'camera_proxy_stream' : 'camera_proxy';
        return fetch(new URL(`api/${endpoint}/${camera.entityId}`, `${baseUrl}/`), {
            headers: { Authorization: `Bearer ${HOME_ASSISTANT_TOKEN}` },
            redirect: 'manual',
            signal
        });
    }
    const rawUrl = kind === 'stream' ? camera.streamUrl : camera.snapshotUrl;
    if (!rawUrl) throw new Error('Für diese Kamera ist kein Live-Stream hinterlegt.');
    const { url, headers } = cameraRequestTarget(rawUrl);
    return fetch(url, { headers, redirect: 'manual', signal });
}

async function fetchCameraSnapshot(camera) {
    if (camera.type === 'rtsp') {
        return { buffer: await grabRtspSnapshot(camera.rtspUrl), contentType: 'image/jpeg', extension: 'jpg' };
    }
    const response = await fetchCameraSource(camera, 'snapshot', AbortSignal.timeout(10000));
    if (!response.ok) throw new Error(`Die Kamera antwortet mit HTTP ${response.status}.`);
    const type = String(response.headers.get('content-type') || '').toLowerCase();
    const match = type.match(/^image\/(jpe?g|png)/);
    if (!match) throw new Error('Die Kamera hat kein Standbild geliefert.');
    if (Number(response.headers.get('content-length')) > MAX_CAMERA_IMAGE_BYTES) throw new Error('Das Kamerabild ist zu groß.');
    const buffer = Buffer.from(await response.arrayBuffer());
    if (!buffer.length || buffer.length > MAX_CAMERA_IMAGE_BYTES) throw new Error('Das Kamerabild ist ungültig.');
    return { buffer, contentType: match[1] === 'png' ? 'image/png' : 'image/jpeg', extension: match[1] === 'png' ? 'png' : 'jpg' };
}

function listCameraEvents() {
    let files = [];
    try {
        files = fs.readdirSync(CAMERA_EVENTS_DIR).filter(file => CAMERA_EVENT_FILE_PATTERN.test(file));
    } catch (error) {
        return [];
    }
    return files.map(file => ({ file, cameraId: file.slice(0, 8), time: Number(file.slice(9, 22)) }))
        .sort((first, second) => second.time - first.time);
}

function pruneCameraEvents(cameraId) {
    listCameraEvents().filter(event => event.cameraId === cameraId).slice(MAX_CAMERA_EVENTS).forEach(event => {
        fs.rmSync(path.join(CAMERA_EVENTS_DIR, event.file), { force: true });
    });
}

async function captureCameraEvent(camera) {
    const last = cameraLastCapture.get(camera.id) || 0;
    if (Date.now() - last < CAMERA_MOTION_COOLDOWN_MS) return;
    cameraLastCapture.set(camera.id, Date.now());
    const image = await fetchCameraSnapshot(camera);
    fs.mkdirSync(CAMERA_EVENTS_DIR, { recursive: true, mode: 0o700 });
    fs.writeFileSync(path.join(CAMERA_EVENTS_DIR, `${camera.id}-${Date.now()}.${image.extension}`), image.buffer, { mode: 0o600 });
    pruneCameraEvents(camera.id);
}

async function pollCameraMotion() {
    if (cameraMotionPolling) return;
    const cameras = getCameras().filter(camera => camera.type === 'home-assistant' && camera.motionEntityId);
    if (!cameras.length || !getHomeAssistantBaseUrl() || !HOME_ASSISTANT_TOKEN) return;
    cameraMotionPolling = true;
    try {
        await Promise.all(cameras.map(async camera => {
            try {
                const entity = await requestHomeAssistant(`api/states/${camera.motionEntityId}`);
                const previous = cameraMotionState.get(camera.id);
                cameraMotionState.set(camera.id, entity.state);
                if (entity.state === 'on' && previous !== undefined && previous !== 'on') await captureCameraEvent(camera);
            } catch (error) {
                console.error(`Bewegungsabfrage für ${camera.name} fehlgeschlagen:`, error.message);
            }
        }));
    } finally {
        cameraMotionPolling = false;
    }
}

setInterval(pollCameraMotion, CAMERA_MOTION_POLL_MS).unref();

app.get('/api/cameras', (req, res) => {
    res.json({
        cameras: getCameras().map(publicCamera),
        homeAssistantConfigured: Boolean(getHomeAssistantBaseUrl() && HOME_ASSISTANT_TOKEN)
    });
});

app.get('/api/cameras/home-assistant', async (req, res) => {
    try {
        const states = await requestHomeAssistant('api/states');
        const label = state => String(state.attributes?.friendly_name || state.entity_id).slice(0, 80);
        const cameras = states.filter(state => /^camera\.[a-z0-9_]+$/.test(state.entity_id))
            .map(state => ({ entityId: state.entity_id, name: label(state) }));
        const motionSensors = states.filter(state => /^binary_sensor\.[a-z0-9_]+$/.test(state.entity_id) &&
            (['motion', 'occupancy', 'moving', 'presence'].includes(state.attributes?.device_class) || /motion|bewegung|person|movement/i.test(state.entity_id)))
            .map(state => ({ entityId: state.entity_id, name: label(state) }));
        const byName = (first, second) => first.name.localeCompare(second.name, 'de');
        res.json({ cameras: cameras.sort(byName), motionSensors: motionSensors.sort(byName) });
    } catch (error) {
        res.status(502).json({ error: error.message || 'Home Assistant konnte nicht abgefragt werden.' });
    }
});

app.post('/api/cameras', (req, res) => {
    try {
        const cameras = getCameras();
        if (cameras.length >= MAX_CAMERAS) return res.status(400).json({ error: `Es sind höchstens ${MAX_CAMERAS} Kameras möglich.` });
        const name = String(req.body?.name || '').trim().slice(0, 40);
        const type = req.body?.type;
        if (!name) return res.status(400).json({ error: 'Bitte gib einen Namen für die Kamera ein.' });
        const camera = { id: crypto.randomBytes(4).toString('hex'), name, type };
        if (type === 'home-assistant') {
            const entityId = String(req.body?.entityId || '');
            const motionEntityId = String(req.body?.motionEntityId || '');
            if (!/^camera\.[a-z0-9_]+$/.test(entityId)) return res.status(400).json({ error: 'Bitte wähle eine Kamera aus Home Assistant aus.' });
            if (motionEntityId && !/^binary_sensor\.[a-z0-9_]+$/.test(motionEntityId)) return res.status(400).json({ error: 'Der Bewegungsmelder ist ungültig.' });
            Object.assign(camera, { entityId, motionEntityId });
        } else if (type === 'rtsp') {
            camera.rtspUrl = parseRtspUrl(req.body?.rtspUrl);
        } else if (type === 'url') {
            camera.snapshotUrl = parseCameraUrl(req.body?.snapshotUrl);
            camera.streamUrl = parseCameraUrl(req.body?.streamUrl);
            if (!camera.snapshotUrl) return res.status(400).json({ error: 'Bitte gib die Adresse des Kamera-Standbilds ein.' });
        } else {
            return res.status(400).json({ error: 'Unbekannte Kameraart.' });
        }
        cameras.push(camera);
        saveCameras(cameras);
        res.status(201).json(publicCamera(camera));
    } catch (error) {
        res.status(400).json({ error: error.message || 'Die Kamera konnte nicht gespeichert werden.' });
    }
});

app.get('/api/cameras/events', (req, res) => {
    const names = Object.fromEntries(getCameras().map(camera => [camera.id, camera.name]));
    res.json({
        events: listCameraEvents().filter(event => names[event.cameraId]).slice(0, 60).map(event => ({
            file: event.file,
            cameraId: event.cameraId,
            cameraName: names[event.cameraId],
            time: new Date(event.time).toISOString()
        }))
    });
});

app.delete('/api/cameras/events', (req, res) => {
    listCameraEvents().forEach(event => fs.rmSync(path.join(CAMERA_EVENTS_DIR, event.file), { force: true }));
    res.json({ success: true });
});

app.get('/api/cameras/events/:file', (req, res) => {
    if (!CAMERA_EVENT_FILE_PATTERN.test(req.params.file)) return res.status(404).end();
    const filePath = path.join(CAMERA_EVENTS_DIR, req.params.file);
    if (!fs.existsSync(filePath)) return res.status(404).end();
    res.set('Cache-Control', 'private, max-age=86400');
    res.type(path.extname(req.params.file)).sendFile(filePath);
});

app.delete('/api/cameras/events/:file', (req, res) => {
    if (!CAMERA_EVENT_FILE_PATTERN.test(req.params.file)) return res.status(404).json({ error: 'Aufnahme nicht gefunden.' });
    fs.rmSync(path.join(CAMERA_EVENTS_DIR, req.params.file), { force: true });
    res.json({ success: true });
});

app.delete('/api/cameras/:id', (req, res) => {
    const cameras = getCameras();
    if (!cameras.some(camera => camera.id === req.params.id)) return res.status(404).json({ error: 'Kamera nicht gefunden.' });
    saveCameras(cameras.filter(camera => camera.id !== req.params.id));
    listCameraEvents().filter(event => event.cameraId === req.params.id)
        .forEach(event => fs.rmSync(path.join(CAMERA_EVENTS_DIR, event.file), { force: true }));
    cameraMotionState.delete(req.params.id);
    res.json({ success: true });
});

app.get('/api/cameras/:id/snapshot', async (req, res) => {
    const camera = getCameras().find(item => item.id === req.params.id);
    if (!camera) return res.status(404).json({ error: 'Kamera nicht gefunden.' });
    try {
        const image = await fetchCameraSnapshot(camera);
        res.set({ 'Cache-Control': 'no-store', 'Content-Type': image.contentType }).send(image.buffer);
    } catch (error) {
        res.status(502).json({ error: error.message || 'Kamerabild nicht verfügbar.' });
    }
});

function streamRtspCamera(camera, req, res) {
    const { spawn } = require('child_process');
    activeCameraStreams++;
    const child = spawn(FFMPEG_PATH, ffmpegRtspArgs(camera.rtspUrl, ['-vf', 'scale=1280:-2', '-r', '8', '-q:v', '6', '-f', 'mpjpeg', '-boundary_tag', 'cam']), { stdio: ['ignore', 'pipe', 'ignore'] });
    let released = false;
    const release = () => {
        if (released) return;
        released = true;
        activeCameraStreams--;
        child.kill('SIGKILL');
    };
    res.on('close', release);
    child.on('error', error => {
        release();
        if (!res.headersSent) res.status(502).json({ error: ffmpegMissingMessage(error) });
        else res.end();
    });
    child.stdout.once('data', () => {
        if (released) return;
        res.set({ 'Cache-Control': 'no-store', 'Content-Type': 'multipart/x-mixed-replace; boundary=cam' });
        res.flushHeaders();
    });
    child.stdout.on('data', chunk => {
        if (res.headersSent && !res.destroyed) res.write(chunk);
    });
    child.on('close', () => {
        release();
        if (!res.headersSent) res.status(502).json({ error: 'Von der Kamera kam kein Bild. Prüfe Adresse, Benutzername und Passwort.' });
        else res.end();
    });
    setTimeout(() => {
        if (!res.headersSent && !released) {
            release();
            res.status(504).json({ error: 'Die Kamera antwortet nicht.' });
        }
    }, 15000).unref();
}

app.get('/api/cameras/:id/stream', async (req, res) => {
    const camera = getCameras().find(item => item.id === req.params.id);
    if (!camera) return res.status(404).json({ error: 'Kamera nicht gefunden.' });
    if (activeCameraStreams >= MAX_CAMERA_STREAMS) return res.status(429).json({ error: 'Es laufen bereits zu viele Live-Streams.' });
    if (camera.type === 'rtsp') return streamRtspCamera(camera, req, res);
    const controller = new AbortController();
    activeCameraStreams++;
    let released = false;
    const release = () => {
        if (released) return;
        released = true;
        activeCameraStreams--;
        controller.abort();
    };
    res.on('close', release);
    try {
        const upstream = await fetchCameraSource(camera, 'stream', controller.signal);
        const type = String(upstream.headers.get('content-type') || '');
        if (!upstream.ok || !upstream.body || !/^(multipart\/x-mixed-replace|image\/)/i.test(type)) {
            release();
            return res.status(502).json({ error: 'Die Kamera liefert keinen Live-Stream.' });
        }
        res.set({ 'Cache-Control': 'no-store', 'Content-Type': type });
        const { Readable } = require('stream');
        const body = Readable.fromWeb(upstream.body);
        body.on('error', () => res.end());
        body.pipe(res);
    } catch (error) {
        release();
        if (!res.headersSent) res.status(502).json({ error: error.message || 'Live-Stream nicht verfügbar.' });
        else res.end();
    }
});

// Geräte-Sync: gemeinsame Daten (Termine, Familie, Aufgaben, Vereine ...) für alle Geräte
const SYNC_FILE = path.join(DATA_DIR, '.sync-data.json');
const SYNC_KEYS = new Set([
    'familien-dashboard-members',
    'familien-dashboard-birthdays',
    'familien-dashboard-calendar-events',
    'familien-dashboard-football-teams',
    'familien-dashboard-custom-tabs',
    'familien-dashboard-tasks',
    'familien-dashboard-habits',
    'familien-dashboard-points'
]);
const MAX_SYNC_VALUE_LENGTH = 1500000;

function loadSyncData() {
    try {
        const saved = JSON.parse(fs.readFileSync(SYNC_FILE, 'utf8'));
        const items = {};
        for (const [key, item] of Object.entries(saved.items || {})) {
            if (SYNC_KEYS.has(key) && typeof item?.value === 'string' && Number.isSafeInteger(item.rev)) items[key] = { value: item.value, rev: item.rev };
        }
        return { rev: Number.isSafeInteger(saved.rev) ? saved.rev : 0, items };
    } catch (error) {
        return { rev: 0, items: {} };
    }
}

const syncData = loadSyncData();

function saveSyncData() {
    const temporaryFile = `${SYNC_FILE}.tmp`;
    fs.writeFileSync(temporaryFile, JSON.stringify(syncData), { encoding: 'utf8', mode: 0o600 });
    fs.renameSync(temporaryFile, SYNC_FILE);
}

app.get('/api/sync', (req, res) => {
    const since = Number.parseInt(req.query.since, 10) || 0;
    const items = Object.fromEntries(Object.entries(syncData.items).filter(([, item]) => item.rev > since));
    res.set('Cache-Control', 'no-store').json({ rev: syncData.rev, items });
});

app.put('/api/sync/:key', (req, res) => {
    const key = req.params.key;
    const value = req.body?.value;
    if (!SYNC_KEYS.has(key)) return res.status(404).json({ error: 'Unbekannter Sync-Eintrag.' });
    if (typeof value !== 'string' || value.length > MAX_SYNC_VALUE_LENGTH) return res.status(400).json({ error: 'Ungültiger Wert.' });
    try {
        JSON.parse(value);
    } catch (error) {
        return res.status(400).json({ error: 'Der Wert ist kein gültiges JSON.' });
    }
    if (syncData.items[key]?.value === value) return res.json({ rev: syncData.items[key].rev });
    syncData.rev++;
    syncData.items[key] = { value, rev: syncData.rev };
    try {
        saveSyncData();
    } catch (error) {
        return res.status(500).json({ error: 'Der Sync-Eintrag konnte nicht gespeichert werden.' });
    }
    res.json({ rev: syncData.rev });
});

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

app.get('/api/home-assistant/status', (req, res) => {
    res.json({
        configured: Boolean(getHomeAssistantBaseUrl() && HOME_ASSISTANT_TOKEN),
        supportedDomains: HOME_ASSISTANT_DOMAINS
    });
});

app.get('/api/home-assistant/weather-settings', (req, res) => {
    res.json(getHomeAssistantWeatherConfig());
});

app.get('/api/home-assistant/weather-sensors', async (req, res) => {
    try {
        const states = await requestHomeAssistant('api/states');
        const sensors = states.filter(entity => entity.entity_id.startsWith('sensor.') && classifyHomeAssistantWeatherSensor(entity)).map(entity => ({
            entityId: entity.entity_id,
            name: entity.attributes?.friendly_name || entity.entity_id,
            kind: classifyHomeAssistantWeatherSensor(entity),
            state: entity.state,
            unit: entity.attributes?.unit_of_measurement || ''
        })).sort((first, second) => first.name.localeCompare(second.name, 'de'));
        res.json({ sensors });
    } catch (error) {
        res.status(503).json({ error: error.message || 'Home-Assistant-Wettersensoren konnten nicht geladen werden.' });
    }
});

app.put('/api/home-assistant/weather-settings', async (req, res) => {
    const fields = req.body?.entities && typeof req.body.entities === 'object' ? req.body.entities : {};
    const entities = Object.fromEntries(HOME_ASSISTANT_WEATHER_FIELDS.map(field => [field, String(fields[field] || '')]));
    if (entities.temperature && !/^sensor\.[a-z0-9_]+$/.test(entities.temperature)) return res.status(400).json({ error: 'Bitte einen gültigen Temperatursensor auswählen.' });
    if (HOME_ASSISTANT_WEATHER_FIELDS.some(field => entities[field] && !/^sensor\.[a-z0-9_]+$/.test(entities[field]))) {
        return res.status(400).json({ error: 'Bitte nur gültige Sensoren auswählen.' });
    }
    if (req.body?.enabled === true && !entities.temperature) return res.status(400).json({ error: 'Für die Home-Assistant-Wetterkarte ist ein Temperatursensor erforderlich.' });
    if (new Set(Object.values(entities).filter(Boolean)).size !== Object.values(entities).filter(Boolean).length) {
        return res.status(400).json({ error: 'Ein Sensor kann nur einem Wetterfeld zugeordnet werden.' });
    }
    try {
        const selectedIds = Object.values(entities).filter(Boolean);
        if (req.body?.enabled === true && selectedIds.length) {
            const states = await requestHomeAssistant('api/states');
            const byId = new Map(states.map(entity => [entity.entity_id, entity]));
            for (const [field, entityId] of Object.entries(entities)) {
                if (!entityId) continue;
                const entity = byId.get(entityId);
                if (!entity) return res.status(400).json({ error: `Sensor ${entityId} wurde in Home Assistant nicht gefunden.` });
                const kind = classifyHomeAssistantWeatherSensor(entity);
                if (kind && kind !== field) return res.status(400).json({ error: `Sensor ${entityId} passt nicht zum Feld ${field}.` });
            }
        }
        const settings = {
            enabled: req.body?.enabled === true,
            stationName: String(req.body?.stationName || 'Netatmo').trim().slice(0, 40) || 'Netatmo',
            entities
        };
        fs.writeFileSync(HOME_ASSISTANT_WEATHER_FILE, JSON.stringify(settings, null, 2), { encoding: 'utf8', mode: 0o600 });
        res.json(settings);
    } catch (error) {
        res.status(503).json({ error: error.message || 'Wetterstation konnte nicht gespeichert werden.' });
    }
});

app.get('/api/home-assistant/weather', async (req, res) => {
    const settings = getHomeAssistantWeatherConfig();
    if (!settings.enabled) return res.json({ enabled: false, settings });
    try {
        const states = await requestHomeAssistant('api/states');
        const stateById = new Map(states.map(entity => [entity.entity_id, entity]));
        const readings = Object.fromEntries(HOME_ASSISTANT_WEATHER_FIELDS.map(field => {
            const entity = stateById.get(settings.entities[field]);
            return [field, entity ? {
                value: entity.state,
                unit: entity.attributes?.unit_of_measurement || '',
                name: entity.attributes?.friendly_name || entity.entity_id
            } : null];
        }));
        res.json({ enabled: true, stationName: settings.stationName, readings });
    } catch (error) {
        res.status(503).json({ error: error.message || 'Wetterdaten konnten nicht geladen werden.' });
    }
});

app.get('/api/home-assistant/entities', async (req, res) => {
    try {
        const states = await requestHomeAssistant('api/states');
        const entities = states.filter(entity => isSupportedHomeAssistantEntityId(entity.entity_id)).map(entity => ({
            entityId: entity.entity_id,
            name: entity.attributes?.friendly_name || entity.entity_id,
            domain: entity.entity_id.split('.')[0],
            state: entity.state
        })).sort((first, second) => first.name.localeCompare(second.name, 'de'));
        res.json({ entities });
    } catch (error) {
        res.status(503).json({ error: error.message || 'Home-Assistant-Geräte konnten nicht geladen werden.' });
    }
});

app.get('/api/home-assistant/selection', (req, res) => {
    res.json(getHomeAssistantDashboardConfig());
});

app.put('/api/home-assistant/selection', async (req, res) => {
    if (!Array.isArray(req.body?.entityIds)) return res.status(400).json({ error: 'Ungültige Geräteauswahl.' });
    const requestedIds = [...new Set(req.body.entityIds.filter(isSupportedHomeAssistantEntityId))].slice(0, 80);
    if (requestedIds.length !== req.body.entityIds.length) return res.status(400).json({ error: `Nur unterstützte Geräte (${HOME_ASSISTANT_DOMAINS.join(', ')}) sind erlaubt (maximal 80).` });
    try {
        if (requestedIds.length) {
            const states = await requestHomeAssistant('api/states');
            const availableIds = new Set(states.map(entity => entity.entity_id));
            if (requestedIds.some(id => !availableIds.has(id))) return res.status(400).json({ error: 'Mindestens ein Gerät wurde in Home Assistant nicht gefunden.' });
        }
        const requestedCategories = Array.isArray(req.body.categories) ? req.body.categories : [DEFAULT_HOME_ASSISTANT_CATEGORY];
        const categories = [...new Set([DEFAULT_HOME_ASSISTANT_CATEGORY, ...requestedCategories
            .filter(category => typeof category === 'string')
            .map(category => category.trim().slice(0, 32))
            .filter(Boolean)])].slice(0, 30);
        if (requestedCategories.length > 30 || categories.length !== requestedCategories.filter(category => typeof category === 'string' && category.trim()).length + (requestedCategories.includes(DEFAULT_HOME_ASSISTANT_CATEGORY) ? 0 : 1)) {
            return res.status(400).json({ error: 'Kategorien müssen eindeutig sein und dürfen maximal 32 Zeichen lang sein (maximal 30 Kategorien).'});
        }
        const requestedAssignments = req.body.entityCategories && typeof req.body.entityCategories === 'object' ? req.body.entityCategories : {};
        const entityCategories = Object.fromEntries(requestedIds.map(entityId => {
            const category = String(requestedAssignments[entityId] || DEFAULT_HOME_ASSISTANT_CATEGORY).trim().slice(0, 32);
            return [entityId, categories.includes(category) ? category : DEFAULT_HOME_ASSISTANT_CATEGORY];
        }));
        const config = { entityIds: requestedIds, categories, entityCategories };
        saveHomeAssistantDashboardConfig(config);
        res.json(config);
    } catch (error) {
        res.status(503).json({ error: error.message || 'Home-Assistant-Auswahl konnte nicht gespeichert werden.' });
    }
});

app.get('/api/home-assistant/selected', async (req, res) => {
    try {
        const config = getHomeAssistantDashboardConfig();
        const selectedIds = new Set(config.entityIds);
        if (!selectedIds.size) return res.json({ entities: [] });
        const states = await requestHomeAssistant('api/states');
        const entities = states.filter(entity => selectedIds.has(entity.entity_id)).map(entity => ({
            entityId: entity.entity_id,
            name: entity.attributes?.friendly_name || entity.entity_id,
            domain: entity.entity_id.split('.')[0],
            category: config.entityCategories[entity.entity_id] || DEFAULT_HOME_ASSISTANT_CATEGORY,
            state: entity.state
        }));
        res.json({ entities });
    } catch (error) {
        res.status(503).json({ error: error.message || 'Home-Assistant-Geräte konnten nicht geladen werden.' });
    }
});

app.post('/api/home-assistant/entities/:entityId', async (req, res) => {
    const entityId = String(req.params.entityId || '');
    const domain = entityId.split('.')[0];
    const action = req.body?.action;
    const actionsByDomain = {
        light: ['turn_on', 'turn_off'],
        switch: ['turn_on', 'turn_off'],
        fan: ['turn_on', 'turn_off'],
        climate: ['turn_on', 'turn_off'],
        cover: ['open_cover', 'close_cover', 'stop_cover']
    };
    if (!isSupportedHomeAssistantEntityId(entityId) || !actionsByDomain[domain]?.includes(action)) {
        return res.status(400).json({ error: 'Ungültige Geräteaktion.' });
    }
    if (!getHomeAssistantDashboardConfig().entityIds.includes(entityId)) return res.status(403).json({ error: 'Dieses Gerät ist nicht für das Dashboard freigegeben.' });
    try {
        await requestHomeAssistant(`api/services/${domain}/${action}`, {
            method: 'POST',
            body: JSON.stringify({ entity_id: entityId })
        });
        res.json({ success: true, entityId, action });
    } catch (error) {
        res.status(503).json({ error: error.message || 'Home-Assistant-Gerät konnte nicht geschaltet werden.' });
    }
});

function isPrivateIPv4(address) {
    if (net.isIP(address) !== 4) return false;
    const [first, second] = address.split('.').map(Number);
    return first === 10 ||
        (first === 172 && second >= 16 && second <= 31) ||
        (first === 192 && second === 168);
}

function getShellyDevicesConfig() {
    try {
        const devices = JSON.parse(fs.readFileSync(SHELLY_DEVICES_FILE, 'utf8'));
        if (!Array.isArray(devices)) throw new Error('Shelly-Konfiguration ist ungültig.');
        if (devices.length > 40 || devices.some(device =>
            !device || typeof device.id !== 'string' ||
            !/^[0-9a-f-]{36}$/i.test(device.id) ||
            typeof device.name !== 'string' || !device.name.trim() ||
            !isPrivateIPv4(device.ip)
        )) throw new Error('Shelly-Konfiguration enthält ungültige Geräteangaben.');
        if (new Set(devices.map(device => device.id)).size !== devices.length ||
            new Set(devices.map(device => device.ip)).size !== devices.length) {
            throw new Error('Shelly-Konfiguration enthält doppelte Geräte-IDs oder IP-Adressen.');
        }
        return devices;
    } catch (error) {
        if (error.code === 'ENOENT') return [];
        throw error;
    }
}

function saveShellyDevicesConfig(devices) {
    fs.writeFileSync(SHELLY_DEVICES_FILE, JSON.stringify(devices, null, 2), { encoding: 'utf8', mode: 0o600 });
}

async function requestShellyJson(ip, endpoint) {
    const response = await fetch(`http://${ip}/${endpoint}`, {
        redirect: 'error',
        signal: AbortSignal.timeout(3500)
    });
    const result = await response.json().catch(() => null);
    if (!response.ok || !result || typeof result !== 'object') {
        throw new Error(`Shelly antwortet mit HTTP ${response.status}.`);
    }
    return result;
}

async function getShellyDeviceStatus(device) {
    let generation;
    let status;
    try {
        const legacyInfo = await requestShellyJson(device.ip, 'shelly');
        if (!legacyInfo.type && Number(legacyInfo.gen) !== 1) throw new Error('Kein Shelly Gen1-Gerät.');
        generation = 1;
        status = await requestShellyJson(device.ip, 'status');
        if (!Array.isArray(status.relays)) throw new Error('Das Gerät stellt keine schaltbaren Relais bereit.');
        return {
            ...device,
            generation,
            online: true,
            switches: status.relays.map((relay, id) => ({ id, on: relay.ison === true }))
        };
    } catch (legacyError) {
        try {
            const info = await requestShellyJson(device.ip, 'rpc/Shelly.GetDeviceInfo');
            generation = Number(info.gen) || 2;
            status = await requestShellyJson(device.ip, 'rpc/Shelly.GetStatus');
            const switches = Object.entries(status)
                .map(([key, value]) => {
                    const match = /^switch:(\d+)$/.exec(key);
                    return match && value && typeof value.output === 'boolean'
                        ? { id: Number(match[1]), on: value.output }
                        : null;
                })
                .filter(Boolean)
                .sort((left, right) => left.id - right.id);
            if (!switches.length) throw new Error('Das Gerät stellt keine schaltbaren Ausgänge bereit.');
            return { ...device, generation, online: true, switches };
        } catch (rpcError) {
            throw new Error(`Shelly unter ${device.ip} nicht erreichbar oder nicht unterstützt (${rpcError.message || legacyError.message}).`);
        }
    }
}

app.get('/api/shelly/devices', async (req, res) => {
    try {
        const devices = getShellyDevicesConfig();
        const statuses = await Promise.all(devices.map(async device => {
            try {
                return await getShellyDeviceStatus(device);
            } catch (error) {
                return { ...device, online: false, error: error.message };
            }
        }));
        res.json({ devices: statuses });
    } catch (error) {
        res.status(500).json({ error: error.message || 'Shelly-Geräte konnten nicht geladen werden.' });
    }
});

app.post('/api/shelly/devices', (req, res) => {
    const name = typeof req.body?.name === 'string' ? req.body.name.trim().slice(0, 40) : '';
    const ip = typeof req.body?.ip === 'string' ? req.body.ip.trim() : '';
    if (!name) return res.status(400).json({ error: 'Bitte einen Gerätenamen eingeben.' });
    if (!isPrivateIPv4(ip)) return res.status(400).json({ error: 'Bitte die lokale IPv4-Adresse des Shelly eingeben.' });
    try {
        const devices = getShellyDevicesConfig();
        if (devices.length >= 40) return res.status(400).json({ error: 'Es können maximal 40 Shelly-Geräte hinzugefügt werden.' });
        if (devices.some(device => device.ip === ip)) return res.status(409).json({ error: 'Diese IP-Adresse ist bereits eingetragen.' });
        const device = { id: crypto.randomUUID(), name, ip };
        devices.push(device);
        saveShellyDevicesConfig(devices);
        res.status(201).json({ device });
    } catch (error) {
        res.status(500).json({ error: error.message || 'Shelly-Gerät konnte nicht gespeichert werden.' });
    }
});

app.delete('/api/shelly/devices/:deviceId', (req, res) => {
    try {
        const devices = getShellyDevicesConfig();
        const remaining = devices.filter(device => device.id !== req.params.deviceId);
        if (remaining.length === devices.length) return res.status(404).json({ error: 'Shelly-Gerät wurde nicht gefunden.' });
        saveShellyDevicesConfig(remaining);
        res.json({ success: true });
    } catch (error) {
        res.status(500).json({ error: error.message || 'Shelly-Gerät konnte nicht entfernt werden.' });
    }
});

app.post('/api/shelly/devices/:deviceId/switches/:switchId', async (req, res) => {
    const switchId = Number(req.params.switchId);
    if (!Number.isInteger(switchId) || switchId < 0 || switchId > 31 || typeof req.body?.on !== 'boolean') {
        return res.status(400).json({ error: 'Ungültiger Schaltbefehl.' });
    }
    try {
        const device = getShellyDevicesConfig().find(item => item.id === req.params.deviceId);
        if (!device) return res.status(404).json({ error: 'Shelly-Gerät wurde nicht gefunden.' });
        const current = await getShellyDeviceStatus(device);
        if (!current.switches.some(item => item.id === switchId)) {
            return res.status(400).json({ error: 'Dieser Schaltkanal ist am Shelly nicht verfügbar.' });
        }
        const endpoint = current.generation === 1
            ? `relay/${switchId}?turn=${req.body.on ? 'on' : 'off'}`
            : `rpc/Switch.Set?id=${switchId}&on=${req.body.on}`;
        await requestShellyJson(device.ip, endpoint);
        const updated = await getShellyDeviceStatus(device);
        res.json({ device: updated });
    } catch (error) {
        res.status(503).json({ error: error.message || 'Shelly konnte nicht geschaltet werden.' });
    }
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