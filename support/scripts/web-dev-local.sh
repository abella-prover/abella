#!/bin/sh
# Launch the local Abella Web development environment in a tmux session.
# The session ends as soon as any pane's process exits.

set -eu

session=${WEB_DEV_SESSION:-abella-web-dev}
port=${WEB_DEV_PORT:-8000}
oauth_port=8787
root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
self=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)/$(basename -- "$0")

die() {
  echo "web-dev-local: $*" >&2
  exit 1
}

quote() {
  printf "'%s'" "$(printf '%s' "$1" | sed "s/'/'\\\\''/g")"
}

free_port() {
  python3 - "$1" <<'EOF'
import socket, sys
sock = socket.socket()
sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
try:
    sock.bind(("127.0.0.1", int(sys.argv[1])))
except OSError:
    sys.exit(1)
EOF
}

# Closing the session only sends SIGHUP, which a child may ignore, so
# signal every pane's process group explicitly first.  Each pane is its
# own session leader, so #{pane_pid} is also the process group id.
teardown() {
  tmux set-hook -u -t "$1" pane-died 2>/dev/null || true
  tmux list-panes -s -t "$1" -F '#{pane_pid}' 2>/dev/null |
    while read -r pid; do
      case $pid in
        '' | *[!0-9]*) continue ;;
      esac
      # dash's kill builtin does not accept a -- separator.
      kill -TERM -"$pid" 2>/dev/null || true
    done
  tmux kill-session -t "$1" 2>/dev/null || true
}

# Inside tmux, switch the current client rather than nesting a new one.
enter_session() {
  if [ -n "${TMUX:-}" ]; then
    tmux switch-client -t "=$1:"
  else
    tmux attach -t "=$1:"
    echo "web-dev-local: session '$1' ended"
  fi
}

if [ "${1:-}" = "--teardown" ]; then
  [ -n "${2:-}" ] || exit 2
  teardown "$2"
  exit 0
fi

command -v tmux >/dev/null 2>&1 || die "tmux is required"
command -v python3 >/dev/null 2>&1 || die "python3 is required"

version=$(tmux -V | sed -e 's/^[^0-9]*//' -e 's/[^0-9.].*$//')
major=${version%%.*}
minor=${version#*.}
minor=${minor%%.*}
case $major in '' | *[!0-9]*) major=0 ;; esac
case $minor in '' | *[!0-9]*) minor=0 ;; esac
if [ "$major" -lt 3 ] || { [ "$major" -eq 3 ] && [ "$minor" -lt 3 ]; }; then
  die "tmux 3.3 or newer is required (found $(tmux -V))"
fi

if tmux has-session -t "$session" 2>/dev/null; then
  attached=$(tmux display-message -p -t "=$session:" '#{session_attached}')
  if [ "${attached:-0}" -gt 0 ]; then
    die "session '$session' is already attached; use: tmux attach -t $session"
  fi
  echo "web-dev-local: attaching to detached session '$session'"
  enter_session "$session"
  exit 0
fi

[ -f "$root/support/oauth-worker/.dev.vars" ] ||
  die "missing support/oauth-worker/.dev.vars"
[ -x "$root/support/oauth-worker/node_modules/.bin/wrangler" ] ||
  die "run: (cd support/oauth-worker && npm ci)"
[ -f "$root/web/abella_web.js" ] ||
  die "web/ is not built; run: make web-dev"
[ -f "$root/web/examples/bundle.json" ] ||
  die "examples bundle missing; run: make web-bundle"
free_port "$port" || die "port $port is already in use"
free_port "$oauth_port" || die "port $oauth_port is already in use"

if [ -f "$root/web/abella_web.js" ] &&
   ! grep -q '127\.0\.0\.1:8787' "$root/web/abella_web.js"; then
  echo "web-dev-local: warning: web/abella_web.js is a production build," >&2
  echo "  so OAuth falls back to PAT.  Run: make web-dev" >&2
fi

tmux new-session -d -s "$session" -n dev -c "$root" "${SHELL:-sh}"
tmux split-window -h -t "$session":0.0 -c "$root/support/oauth-worker" \
  'npm run dev'
tmux split-window -v -t "$session":0.1 -c "$root/web" \
  "python3 -m http.server $port --bind 127.0.0.1"
tmux select-layout -t "$session" main-vertical

tmux set-option -wt "$session" remain-on-exit on
tmux set-option -wt "$session" pane-border-status top
tmux select-pane -t "$session":0.0 -T shell
tmux select-pane -t "$session":0.1 -T worker
tmux select-pane -t "$session":0.2 -T server

# A dead pane only closes itself, so the hook tears down the session.
tmux set-hook -t "$session" pane-died \
  "run-shell -b $(quote "$self --teardown $session")"
tmux select-pane -t "$session":0.0

# The dev OAuth App only allows the loopback origin.
tmux set-option -t "$session" status-right " http://127.0.0.1:$port/ "

echo "web-dev-local: open http://127.0.0.1:$port/ (not localhost)"
enter_session "$session"
