import { readFile } from 'node:fs/promises';
import { resolve, isAbsolute } from 'node:path';
import { homedir } from 'node:os';
import type { LayoutServerLoad } from './$types';
import { EMPTY_PROJECT_DATA } from '$lib/data-empty';
import type { ProjectData } from '$lib/types';

const DEFAULT_PROJECT_PATH = '/Users/jonathangadeaharder/projects/phd/lean-runtime-analysis';

function expandHome(p: string): string {
  if (p.startsWith('~/')) return resolve(homedir(), p.slice(2));
  if (p === '~') return homedir();
  return p;
}

export const load: LayoutServerLoad = async ({ url }) => {
  const requested = url.searchParams.get('project')
    ?? process.env.MATHPROVER_PROJECT_PATH
    ?? DEFAULT_PROJECT_PATH;

  const root = isAbsolute(requested) ? requested : resolve(process.cwd(), expandHome(requested));
  const graphFile = resolve(root, '.mathprover/graph.json');

  try {
    const raw = await readFile(graphFile, 'utf-8');
    const parsed = JSON.parse(raw) as Partial<ProjectData>;
    const data: ProjectData = { ...EMPTY_PROJECT_DATA, ...parsed } as ProjectData;
    return { projectData: data, projectRoot: root, error: null as string | null };
  } catch (err) {
    return {
      projectData: EMPTY_PROJECT_DATA,
      projectRoot: root,
      error: `Failed to load ${graphFile}: ${(err as Error).message}`,
    };
  }
};
