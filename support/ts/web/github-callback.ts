// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import {
  OAUTH_CALLBACK_TYPE,
  parseOAuthCallback,
  type OAuthCallback,
} from "./oauth-callback";

const status = document.getElementById("status");

function show(message: string): void {
  if (status) status.textContent = message;
}

function clearQuery(): void {
  history.replaceState(null, "", window.location.pathname);
}

const callback = parseOAuthCallback(window.location.search);
const opener = window.opener;

if (opener && opener !== window) {
  const payload: OAuthCallback = {
    type: OAUTH_CALLBACK_TYPE,
    code: callback.code,
    state: callback.state,
    error: callback.error,
    errorDescription: callback.errorDescription,
  };
  let posted = false;
  try {
    opener.postMessage(payload, window.location.origin);
    posted = true;
  } catch {
    // The opener is gone; fall through to the manual message.
  }
  clearQuery();
  if (posted) {
    window.setTimeout(() => {
      window.close();
      window.setTimeout(() => {
        if (!window.closed) show("You can close this window.");
      }, 100);
    }, 50);
  } else {
    show("Start from Abella Web to finish GitHub sign-in.");
  }
} else {
  clearQuery();
  show("Start from Abella Web to finish GitHub sign-in.");
}
