import { json } from '@sveltejs/kit';
import type { RequestHandler } from './$types';
import { enrichGraph } from '$lib/server/project';
import { resolveRootFromRequest } from '$lib/server/dispatch';

export const GET: RequestHandler = async ({ url }) => {
  const root = resolveRootFromRequest(url);
  try {
    const data = await enrichGraph(root);
    return json({ data, projectRoot: root, error: null });
  } catch (err) {
    return json({ data: null, projectRoot: root, error: (err as Error).message }, { status: 500 });
  }
};
