# Abella MCP server (`abella_mcp`)

`abella_mcp` is a stdio Model Context Protocol (MCP) server for
Abella. It lets agentic coding harnesses incrementally check
`.thm`/`.thmod` files, inspect proof states, probe tactics
speculatively, and look up lemmas without driving the `abella`
batch CLI by hand.

It runs over stdio and takes no arguments:

```sh
abella_mcp
```

## Prerequisites

Install Abella so that `abella_mcp` is on your `PATH`:

```sh
opam pin abella .
command -v abella_mcp
```

If you do not want to install, use the built binary directly:

```sh
dune build @default
./_build/default/bin/abella_mcp.exe
```

Prefer an absolute path in harness configs when `abella_mcp` is
not on `PATH`, for example `/home/user/work/abella/_build/
default/bin/abella_mcp.exe` or the opam bin path. Find it with:

```sh
command -v abella_mcp
```

## Tools

| Tool | Purpose |
| ---- | ------- |
| `check_file` | Check a `.thm`/`.thmod` file incrementally. |
| `get_state` | Get hypotheses, variables, and goals at a 1-based line. |
| `try_tactic` | Probe one tactic at a line; cached state is unchanged. |
| `search_lemmas` | Substring search over in-scope lemma names and statements. |
| `show` | Show a theorem, sealed type, or inductive definition. |
| `reset` | Clear the incremental session cache. |

Common arguments are `path` (required), `line`, `tactic`,
`query`, `name`, and optional `contents`, `strict`, and
`name_mode`. File paths are resolved by the server process, so
use workspace-relative paths from a fixed working directory or
absolute paths.

## Codex

Codex reads `~/.codex/config.toml` (shared by CLI, IDE
extension, and desktop app) or project-scoped
`.codex/config.toml` in trusted projects.

CLI (recommended):

```sh
codex mcp add abella -- abella_mcp
codex mcp list
```

Manual global config (`~/.codex/config.toml`):

```toml
[mcp_servers.abella]
command = "abella_mcp"
args = []
```

Use an absolute `command` when `abella_mcp` is not on `PATH`.
Restart the client and check the server with `codex mcp list`
or `/mcp`.

## Claude Code

CLI (run outside a `claude` session):

```sh
claude mcp add abella -- abella_mcp
claude mcp list
```

Use `--scope user` for every project, or `--scope project`
to share through `.mcp.json`:

```sh
claude mcp add --scope user abella -- abella_mcp
claude mcp add --scope project abella -- abella_mcp
```

Manual project config (`.mcp.json` at the project root):

```json
{
  "mcpServers": {
    "abella": {
      "type": "stdio",
      "command": "abella_mcp",
      "args": []
    }
  }
}
```

Local scope is the default and lives under the project entry
in `~/.claude.json`; user scope lives under the top-level
`mcpServers` key there. Verify with `claude mcp list` or `/mcp`
inside a session and approve the server if prompted.

## Gemini Antigravity

Antigravity keeps one global MCP file:

- macOS/Linux: `~/.gemini/config/mcp_config.json`
- Windows: `C:\Users\<USERNAME>\.gemini\config\mcp_config.json`

You can also open it from the IDE via `...` (Agent panel) >
`MCP Servers` > `Manage MCP Servers` > `View raw config`.
Add:

```json
{
  "mcpServers": {
    "abella": {
      "command": "abella_mcp",
      "args": []
    }
  }
}
```

Restart Antigravity completely, then verify under `...` >
`MCP Servers` that `abella` is listed with its tools. Keep
the total enabled tool count modest; the IDE recommends
staying under about 50 tools.

## OpenCode

CLI (run in the project to use):

```sh
opencode mcp add abella -- abella_mcp
opencode mcp list
```

Add `--global` to store it in the user config instead of the
project config.

Manual config uses `mcp.servers` (note the nesting). Project
file is `opencode.json` or `opencode.jsonc`; global file is
`~/.config/opencode/opencode.json`:

```json
{
  "$schema": "https://opencode.ai/config.json",
  "mcp": {
    "servers": {
      "abella": {
        "type": "local",
        "command": ["abella_mcp"]
      }
    }
  }
}
```

Verify with `opencode mcp list` or `/mcps` inside OpenCode.
Remove it by deleting the entry from whichever file defines
it.

## Pi

Pi reads user servers from `~/.pi/agent/mcp.json` and project
servers from `.pi/mcp.json` (after project trust is granted).
A project entry with the same name overrides the user entry.

CLI (user level by default):

```sh
pi mcp add abella -- abella_mcp
pi mcp list
```

Use `--local` (or `-l`) for the project file:

```sh
pi mcp add --local abella -- abella_mcp
```

Manual user config (`~/.pi/agent/mcp.json`):

```json
{
  "mcpServers": {
    "abella": {
      "command": "abella_mcp",
      "args": []
    }
  }
}
```

The same shape goes in `.pi/mcp.json` for a project server.
`command` is one executable and `args` holds its arguments;
it is not a shell string. Verify with `pi mcp list` (exit
status 1 means an invalid entry or a failed connection) or
`/mcp` inside a session, then `/reload` if you edited the
file outside the session.

Note: Pi "skills" (`~/.pi/agent/skills/`, `.pi/skills/`) are
prompt packs, not servers. Registering the entry above is
sufficient; no skill wrapper is needed.

## Verification and troubleshooting

- Check the binary first: `abella_mcp --help` should print
  usage and exit. If a harness reports "failed to connect",
  run the configured command by hand in a terminal.
- Use absolute paths for `command` and for tool `path`
  arguments when the harness and server disagree on the
  working directory.
- Keep only one definition per harness scope: duplicates
  across global/project configs override or collide.
- After hand-editing a config file, restart the harness (or
  run its reload command) and re-list MCP servers.
- Only enable `abella_mcp` where you need Abella proofs;
  every connected server costs model context.
