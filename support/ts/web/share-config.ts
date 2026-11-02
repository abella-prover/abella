// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Origins that may serve a `?zip=` handoff.  The production Worker is
// public; the loopback origin is the `wrangler dev` Worker.  There is
// deliberately no query-parameter or storage override.

export const SHARE_WORKER_ORIGINS: readonly string[] = [
  "https://zips.abella-prover.org",
  "http://127.0.0.1:8788",
];
