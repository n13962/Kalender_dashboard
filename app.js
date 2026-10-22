// Live-Uhr oben rechts
function updateClock() {
    const now = new Date();
    const timeString = now.toLocaleTimeString('de-DE', { hour: '2-digit', minute: '2-digit' });
    document.getElementById('clock').innerText = timeString;
}
setInterval(updateClock, 1000);
updateClock();

// Profile und Einstellungen vom Server laden
function loadSettingsAndProfiles() {
    fetch('/api/settings')
        .then(res => res.json())
        .then(settings => {
            const memberNames = settings.members.split(',').map(m => m.trim());
            const colors = ['#3b82f6', '#ec4899', '#eab308', '#10b981', '#8b5cf6'];
            
            const profileContainer = document.getElementById('member-profiles');
            profileContainer.innerHTML = '';
            
            memberNames.forEach((name, index) => {
                const badge = document.createElement('div');
                badge.className = 'profile-badge';
                badge.style.backgroundColor = colors[index % colors.length];
                badge.innerText = name;
                profileContainer.appendChild(badge);
            });

            // Felder im Modal mit den aktuellen Werten vorbefüllen
            document.getElementById('setting-ical').value = settings.icalUrl;
            document.getElementById('setting-members').value = settings.members;
        });
}

// Kalender-Daten laden
function loadCalendar() {
    fetch('/api/calendar')
        .then(res => res.json())
        .then(events => {
            const calendarContainer = document.getElementById('calendar-view');
            if (!events.length) {
                calendarContainer.innerHTML = `<p>Keine anstehenden Termine gefunden.</p>`;
                return;
            }

            let html = '<ul class="event-list">';
            events.forEach(ev => {
                const startDate = new Date(ev.start).toLocaleDateString('de-DE', {
                    day: '2-digit', month: '2-digit', year: 'numeric'
                });
                html += `
                    <li class="event-item">
                        <span class="event-date">${startDate}</span>
                        <span class="event-title">${ev.summary}</span>
                    </li>
                `;
            });
            html += '</ul>';
            calendarContainer.innerHTML = html;
        });
}

// To-Do Logik
function loadTodos() {
    fetch('/api/todos')
        .then(res => res.json())
        .then(todos => {
            const todoList = document.getElementById('todo-list');
            if (!todos.length) {
                todoList.innerHTML = `<li style="color: #64748b; justify-content: center;">Keine Aufgaben vorhanden</li>`;
                return;
            }

            todoList.innerHTML = '';
            todos.forEach(todo => {
                const li = document.createElement('li');
                li.innerText = todo.text;
                if (todo.completed) li.classList.add('completed');
                li.addEventListener('click', () => {
                    fetch(`/api/todos/${todo.id}`, { method: 'DELETE' }).then(() => loadTodos());
                });
                todoList.appendChild(li);
            });
        });
}

const inputField = document.getElementById('todo-input');
const addButton = document.getElementById('todo-add-btn');

function addTodo() {
    const text = inputField.value;
    if (!text) return;
    fetch('/api/todos', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ text })
    }).then(() => { inputField.value = ''; loadTodos(); });
}

addButton.addEventListener('click', addTodo);
inputField.addEventListener('keypress', (e) => { if (e.key === 'Enter') addTodo(); });

// --- EINSTELLUNGS-MODAL STEUERUNG ---
const modal = document.getElementById('settings-modal');
const settingsBtn = document.getElementById('settings-btn');
const closeBtn = document.getElementById('settings-close');
const saveBtn = document.getElementById('settings-save');

// Öffnen beim Klick aufs Zahnrad
settingsBtn.addEventListener('click', () => {
    modal.style.display = 'flex';
    modal.classList.remove('hidden');
});

// Schließen beim Klick auf "Abbrechen"
closeBtn.addEventListener('click', () => {
    modal.style.display = 'none';
    modal.classList.add('hidden');
});

// Speichern und Schließen
saveBtn.addEventListener('click', (e) => {
    e.preventDefault();

    const icalUrl = document.getElementById('setting-ical').value;
    const members = document.getElementById('setting-members').value;

    fetch('/api/settings', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ icalUrl, members })
    })
    .then(res => res.json())
    .then(() => {
        modal.style.display = 'none';
        modal.classList.add('hidden');
        loadSettingsAndProfiles();
        loadCalendar(); // Kalender sofort mit dem neuen Link neu laden
    })
    .catch(err => {
        console.error('Fehler beim Speichern der Einstellungen:', err);
    });
});

// Initialer Start beim Laden der Seite
loadSettingsAndProfiles();
loadCalendar();
loadTodos();