// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// The Worker URL is fixed at build time.  Production uses the public
// Worker; `npm run web:build:dev` defines the loopback URL.  There is
// deliberately no query-parameter or storage override: a malicious
// Worker could receive authorization codes.

declare const __GITHUB_OAUTH_WORKER__: string | undefined;

export const GITHUB_OAUTH_WORKER =
  typeof __GITHUB_OAUTH_WORKER__ === "string"
    ? __GITHUB_OAUTH_WORKER__
    : "https://oauth.abella-prover.org";
