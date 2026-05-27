import { json } from '@sveltejs/kit';
import type { RequestHandler } from './$types';
import { readRuns, resolveRootFromRequest } from '$lib/server/dispatch';

export const GET: RequestHandler = async ({ url }) => {
  const root = resolveRootFromRequest(url);
  const runs = await readRuns(root);
  return json({ runs });
};
