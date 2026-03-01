# Q: like if I'm already in the folder of the repo and then I do claude terminal cmd and in claude I do /init what does that do? PS: I'm also trying to understand how to initialize .CLAUDE in my new repo.

Answer from Claude Code's special ChatBot:

The `/init` command inside Claude Code **generates a starter CLAUDE.md file** for your project. It analyzes your codebase to detect build systems, test frameworks, and code patterns, then creates a CLAUDE.md with build commands, test instructions, and project conventions it discovers.

If a CLAUDE.md already exists, `/init` suggests improvements rather than overwriting it.

**To initialize `.claude` in a new repo:**
1. Run `claude` in your repo folder
2. Type `/init` in the interactive session
3. Claude will create a CLAUDE.md file with detected project settings

This is different from the `--init` CLI flag, which runs initialization *hooks* before starting.

```suggestions
(Best practices for CLAUDE.md)[/en/best-practices]
(Memory and CLAUDE.md files)[/en/memory]
```

---

# Claude in yolo mode `claude --dangerously-skip-permissions`

The `--dangerously-skip-permissions` flag **skips all permission prompts** when running Claude Code. This means Claude can execute commands, edit files, and perform actions without asking for your approval each time.

**Use with caution** — this bypasses safety checks. It's typically used for:
- Automated/CI pipelines
- Trusted, sandboxed environments
- Headless operation where no human is present to approve

There's also `--allow-dangerously-skip-permissions` which *enables* the option without immediately activating it, allowing you to compose it with other flags like `--permission-mode plan`.

```suggestions
(Permissions documentation)[/en/permissions]
(CLI reference)[/en/cli-reference]
```