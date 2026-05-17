/* tslint:disable */
/* eslint-disable */

export function _start(): void;

/**
 * Return the dep-graph DOT + execution summary for preset `idx` as JSON:
 * `{"name": "…", "dep_graph_dot": "…", "execution_summary": "…"}`
 *
 * Returns `null` (JSON) if `idx` is out of range.
 */
export function get_preset_dot(idx: number): string;

/**
 * Return all step snapshots for preset `idx` as a JSON array.
 *
 * Each element: `{"step": N, "psi_stars": […], "active_ray": "…", "dot": "…", "is_final": bool}`
 *
 * Returns `"[]"` if `idx` is out of range.
 */
export function get_preset_steps(idx: number): string;

/**
 * Return all presets as a JSON array:
 * `[{"id": 0, "name": "…", "description": "…"}, …]`
 */
export function list_presets(): string;

/**
 * Return the number of available presets.
 */
export function preset_count(): number;

export type InitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;

export interface InitOutput {
    readonly memory: WebAssembly.Memory;
    readonly get_preset_dot: (a: number) => [number, number];
    readonly get_preset_steps: (a: number) => [number, number];
    readonly list_presets: () => [number, number];
    readonly preset_count: () => number;
    readonly _start: () => void;
    readonly __wbindgen_free: (a: number, b: number, c: number) => void;
    readonly __wbindgen_malloc: (a: number, b: number) => number;
    readonly __wbindgen_realloc: (a: number, b: number, c: number, d: number) => number;
    readonly __wbindgen_externrefs: WebAssembly.Table;
    readonly __wbindgen_start: () => void;
}

export type SyncInitInput = BufferSource | WebAssembly.Module;

/**
 * Instantiates the given `module`, which can either be bytes or
 * a precompiled `WebAssembly.Module`.
 *
 * @param {{ module: SyncInitInput }} module - Passing `SyncInitInput` directly is deprecated.
 *
 * @returns {InitOutput}
 */
export function initSync(module: { module: SyncInitInput } | SyncInitInput): InitOutput;

/**
 * If `module_or_path` is {RequestInfo} or {URL}, makes a request and
 * for everything else, calls `WebAssembly.instantiate` directly.
 *
 * @param {{ module_or_path: InitInput | Promise<InitInput> }} module_or_path - Passing `InitInput` directly is deprecated.
 *
 * @returns {Promise<InitOutput>}
 */
export default function __wbg_init (module_or_path?: { module_or_path: InitInput | Promise<InitInput> } | InitInput | Promise<InitInput>): Promise<InitOutput>;
