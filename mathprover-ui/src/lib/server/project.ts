import { readFile } from 'node:fs/promises';
import { homedir } from 'node:os';
import { isAbsolute, resolve } from 'node:path';
import { spawn } from 'node:child_process';
import type { ProjectData } from '$lib/types';
import { EMPTY_PROJECT_DATA } from '$lib/data-empty';

const DEFAULT_PROJECT_PATH = '/Users/jonathangadeaharder/projects/phd/lean-runtime-analysis';

export function expandHome(p: string): string {
  if (p.startsWith('~/')) return resolve(homedir(), p.slice(2));
  if (p === '~') return homedir();
  return p;
}

export function resolveProjectRoot(raw?: string | null): string {
  const requested = raw ?? process.env.MATHPROVER_PROJECT_PATH ?? DEFAULT_PROJECT_PATH;
  return isAbsolute(requested) ? requested : resolve(process.cwd(), expandHome(requested));
}

export function graphPath(root: string): string {
  return resolve(root, '.mathprover/graph.json');
}

export async function loadGraph(root: string): Promise<ProjectData> {
  const raw = await readFile(graphPath(root), 'utf-8');
  const parsed = JSON.parse(raw) as Partial<ProjectData>;
  return { ...EMPTY_PROJECT_DATA, ...parsed } as ProjectData;
}

export async function enrichGraph(root: string): Promise<ProjectData> {
  const base = await loadGraph(root);
  const enriched = await runPythonJson<ProjectData>(
    root,
    ['scripts/index_runs.py', '--root', root, '--graph'],
  );
  if (!enriched) return base;
  return {
    ...base,
    ...enriched,
    project: { ...base.project, ...enriched.project },
    nodes: enriched.nodes?.length ? enriched.nodes : base.nodes,
    activeAgent: enriched.activeAgent ?? base.activeAgent,
  };
}

export function pythonBin(root: string): string {
  const venv = resolve(root, 'agents/.venv/bin/python');
  return venv;
}

export function runPythonJson<T>(root: string, args: string[]): Promise<T | null> {
  return new Promise((resolvePromise) => {
    const proc = spawn(pythonBin(root), args, {
      cwd: root,
      env: { ...process.env },
    });
    let out = '';
    let err = '';
    proc.stdout.on('data', (d) => (out += d.toString()));
    proc.stderr.on('data', (d) => (err += d.toString()));
    proc.on('close', (code) => {
      if (code !== 0 || !out.trim()) {
        if (err) console.error('[python]', err.trim());
        resolvePromise(null);
        return;
      }
      try {
        resolvePromise(JSON.parse(out) as T);
      } catch {
        resolvePromise(null);
      }
    });
  });
}

export function runPythonText(root: string, args: string[]): Promise<{ code: number; out: string; err: string }> {
  return new Promise((resolvePromise) => {
    const proc = spawn(pythonBin(root), args, {
      cwd: root,
      env: { ...process.env },
    });
    let out = '';
    let err = '';
    proc.stdout.on('data', (d) => (out += d.toString()));
    proc.stderr.on('data', (d) => (err += d.toString()));
    proc.on('close', (code) => resolvePromise({ code: code ?? 1, out, err }));
  });
}

export function utcRunId(): string {
  const d = new Date();
  const pad = (n: number) => String(n).padStart(2, '0');
  return (
    d.getUTCFullYear() +
    pad(d.getUTCMonth() + 1) +
    pad(d.getUTCDate()) +
    'T' +
    pad(d.getUTCHours()) +
    pad(d.getUTCMinutes()) +
    pad(d.getUTCSeconds()) +
    'Z'
  );
}

export function projectQuery(url: URL): string {
  return url.searchParams.get('project') ?? '';
}
