import { json } from '@sveltejs/kit';
import type { RequestHandler } from './$types';
import { readLogTail, resolveRootFromRequest } from '$lib/server/dispatch';

export const GET: RequestHandler = async ({ url, params }) => {
  const root = resolveRootFromRequest(url);
  const logPath = url.searchParams.get('path');
  const offset = Number(url.searchParams.get('offset') ?? '0');
  if (!logPath) return json({ error: 'path query required' }, { status: 400 });
  const { text, size } = await readLogTail(root, logPath, offset);
  return json({ id: params.id, text, size, offset });
};
