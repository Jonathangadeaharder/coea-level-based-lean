import { spawn, type ChildProcess } from 'node:child_process';
import { resolve } from 'node:path';
import type { RunRecord } from '$lib/types';
import { pythonBin, resolveProjectRoot, utcRunId } from './project';

const activeProcesses = new Map<string, ChildProcess>();

export async function previewRoute(
  root: string,
  nodeId: string,
  prover: string,
): Promise<{ folder: string; prover: string; reason: string } | null> {
  const { spawn: sp } = await import('node:child_process');
  return new Promise((resolvePromise) => {
    const proc = sp(pythonBin(root), ['agents/preview.py', nodeId, prover], {
      cwd: root,
      env: { ...process.env },
    });
    let out = '';
    proc.stdout.on('data', (d) => (out += d.toString()));
    proc.on('close', (code) => {
      if (code !== 0) return resolvePromise(null);
      try {
        resolvePromise(JSON.parse(out));
      } catch {
        resolvePromise(null);
      }
    });
  });
}

export function spawnDispatch(opts: {
  root: string;
  nodeId: string;
  prover: string;
  skipVerify?: boolean;
  runId?: string;
}): { runId: string; pid: number } {
  const runId = opts.runId ?? utcRunId();
  const args = [
    'agents/dispatch.py',
    '--node',
    opts.nodeId,
    '--prover',
    opts.prover,
    '--run-id',
    runId,
  ];
  if (opts.skipVerify) args.push('--skip-verify');

  const proc = spawn(pythonBin(opts.root), args, {
    cwd: opts.root,
    env: { ...process.env },
    detached: false,
    stdio: ['ignore', 'pipe', 'pipe'],
  });

  activeProcesses.set(runId, proc);
  proc.on('close', () => activeProcesses.delete(runId));

  return { runId, pid: proc.pid ?? 0 };
}

export function cancelRun(runId: string): boolean {
  const proc = activeProcesses.get(runId);
  if (!proc?.pid) return false;
  proc.kill('SIGTERM');
  activeProcesses.delete(runId);
  return true;
}

export async function readRuns(root: string): Promise<RunRecord[]> {
  const { readdir, readFile } = await import('node:fs/promises');
  const runsDir = resolve(root, '.mathprover/runs');
  try {
    const files = (await readdir(runsDir)).filter((f) => f.endsWith('.json'));
    const runs: RunRecord[] = [];
    for (const f of files) {
      try {
        runs.push(JSON.parse(await readFile(resolve(runsDir, f), 'utf-8')) as RunRecord);
      } catch {
        /* skip corrupt */
      }
    }
    return runs.sort((a, b) => b.started_at.localeCompare(a.started_at));
  } catch {
    return [];
  }
}

export async function readLogTail(root: string, logPath: string, offset = 0): Promise<{ text: string; size: number }> {
  const { readFile, stat } = await import('node:fs/promises');
  const full = resolve(root, logPath);
  try {
    const st = await stat(full);
    const buf = await readFile(full);
    const text = buf.slice(Math.min(offset, buf.length)).toString('utf-8');
    return { text, size: st.size };
  } catch {
    return { text: '', size: 0 };
  }
}

export async function goedelLockStatus(root: string): Promise<{ locked: boolean; pid?: string }> {
  const { readFile, access } = await import('node:fs/promises');
  const lockPath = resolve(root, '.mathprover/locks/goedel.lock');
  try {
    await access(lockPath);
    const content = await readFile(lockPath, 'utf-8');
    const m = content.match(/pid=(\d+)/);
    return { locked: true, pid: m?.[1] };
  } catch {
    return { locked: false };
  }
}

export function resolveRootFromRequest(url: URL): string {
  return resolveProjectRoot(url.searchParams.get('project'));
}
