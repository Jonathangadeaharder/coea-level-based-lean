import { json } from '@sveltejs/kit';
import type { RequestHandler } from './$types';
import { enrichGraph, resolveProjectRoot } from '$lib/server/project';
import { runPythonText } from '$lib/server/project';

export const POST: RequestHandler = async ({ url }) => {
  const root = resolveProjectRoot(url.searchParams.get('project'));
  const backfill = await runPythonText(root, ['scripts/index_runs.py', '--root', root, '--backfill']);
  const build = await runPythonText(root, ['scripts/bootstrap_graph.py']);
  if (build.code !== 0) {
    await runPythonText(root, ['scripts/build_graph.py', '--root', root]);
  }
  let data = null;
  let error: string | null = null;
  try {
    data = await enrichGraph(root);
  } catch (err) {
    error = (err as Error).message;
  }
  return json({
    ok: build.code === 0,
    backfill: backfill.out.trim(),
    build: build.out.trim() || build.err.trim(),
    data,
    error,
  });
};
