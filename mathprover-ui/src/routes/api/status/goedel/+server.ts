import { json } from '@sveltejs/kit';
import type { RequestHandler } from './$types';
import { goedelLockStatus, resolveRootFromRequest } from '$lib/server/dispatch';

export const GET: RequestHandler = async ({ url }) => {
  const root = resolveRootFromRequest(url);
  const lock = await goedelLockStatus(root);
  return json(lock);
};
