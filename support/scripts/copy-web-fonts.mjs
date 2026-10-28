// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Copy the bundled Fira Code font and its license from the npm package.

import { copyFileSync, mkdirSync, rmSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const packageRoot = fileURLToPath(
  new URL("../node_modules/firacode/", import.meta.url)
);
const webFonts = fileURLToPath(
  new URL("../../web/fonts/", import.meta.url)
);
const fontSource = join(
  packageRoot,
  "distr/woff2/FiraCode-VF.woff2"
);
const licenseSource = join(packageRoot, "LICENSE");

rmSync(webFonts, { recursive: true, force: true });
mkdirSync(webFonts, { recursive: true });
copyFileSync(fontSource, join(webFonts, "FiraCode-VF.woff2"));
copyFileSync(licenseSource, join(webFonts, "OFL.txt"));
