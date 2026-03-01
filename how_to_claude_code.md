# Q: like if I'm already in the folder of the repo and then I do claude terminal cmd and in claude I do /init what does that do? PS: I'm also trying to understand how to initialize .CLAUDE in my new repo.

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