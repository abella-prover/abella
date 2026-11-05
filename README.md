Quick Start
===========

The easiest way to install Abella is using [OPAM][opam] (version 2.1+).

[opam]: https://opam.ocaml.org

1. Go to the topmost directory of the clone of this repository,
   i.e., the location of this very `README.md` file.
2. Run: `opam pin abella .` (note the final period)
3. When prompted by OPAM, say `yes` to install Abella.
4. Whenever you do a `git pull`, also do: `opam reinstall abella`.

To uninstall Abella using OPAM, do:

1. Run: `opam remove abella`.
2. Then run: `opam unpin abella`.


Abella Web
==========

Instead of running Abella locally, you can also use [Abella
Web](https://abella-prover.org/web/), which is a development environment for
Abella that runs entirely in your browser. Your files never leave your browser
and never reach the internet.

It has optional Github integration if you want to load/commit your development
using a Github-hosted repository instead of your local browser.

You can also build and deploy the browser interface locally. See
[web/README.md](web/README.md). You probably don't need to do this if you're not
an Abella developer.


More Information
================

Use the following walkthrough for an introduction to using Abella:

  https://abella-prover.org/walkthrough.html

More information on Abella is available at

  https://abella-prover.org/


Bugs, Feature Requests, and Issues
==================================

Please report all bugs, feature requests, and issues on the GitHub
issue tracker for Abella, available from:

  https://github.com/abella-prover/abella/issues

Discussion of Abella and its uses happens on this mailing list.

  http://groups.google.com/group/abella-theorem-prover
