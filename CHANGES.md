Changes in 2.1.0-dev from 2.0.8
-------------------------------

Additions

* Added the `compute` tactic for performing asynchronous
  computation on hypotheses. Detailed examples can be found
  in the `examples/compute/` subdirectory.

Changes

* Abella now compiles with Dune version 3.7 or later.  
  (#154, reported by @yurivict)
* Abella is now byte-compiled for ppc32 and ppc64.  
  (#151, reporeted by @barracuda156)

Bugfixes

* File names in error locations were not correct  
  (PR #157, contributed by @wikku)
* Incorrect lambda-prefix for non-Llambda unification problems  
  (#155, report + fix by @wikku)
* `Import ... with` now requires the replacements for the declared
  predicates in the importee to be pairwise distinct.  
  (#152, discovered in discussions with Farah Al Wardani @innofarah and Dale
  Miller @thatdalemiller)  
  ***SOUNDNESS BUG***
* `Import ... with` performs the replacements simultaneously. (#153)


Changes in 2.0.8 from 2.0.7
---------------------------

Possibly breaking changes

* Abella now uses [Dune][dune] instead of [ocamlbuild][ocamlbuild].  
  (#138, additional contributions: Chase Johnson)
* The command line for the `abella` command has slightly changed.
  - The old `-v` option is removed; use `--version` instead.
  - The old `-nr` option is removed; use `--non-recursive` instead.
* In batch mode, Abella always produces `file.thc` from `file.thm`.
* Abella's parser changed from [ocamlyacc][ocamlyacc] to [Menhir][menhir]
* Abella's annotation mode (`-a`) now produces annotations in JSON format
  instead of in HTML fragments. The JSON schema should be seen as
  experimental for now and subject to change in the future.
* Abella's dependency generator option (`-M`) has now been moved to
  a separate program (see "Additions" below).

[dune]: https://dune.build
[ocamlbuild]: https://github.com/ocaml/ocamlbuild/
[ocamlyacc]: https://v2.ocaml.org/manual/lexyacc.html#s%3Aocamlyacc-overview
[menhir]: http://gallium.inria.fr/~fpottier/menhir/

Additions

* **Documentation Generation (`abella_doc`)**: There is now a special program
  called `abella_doc` that can be used to convert a collection of Abella
  sources into HTML pages that resemble the Abella examples on the
  web-site: https://abella-prover.org/examples/
  
  Run `abella_doc --help` for usage instructions.
* **Dependency Generation (`abella_dep`)**: There is now a special
  program called `abella_dep` that can be used to generate a
  `Makefile`-based dependency graph. Executing `make` on that
  `Makefile` will recompile all the Abella sources specified to
  `abella_dep`. This `Makefile` can be used in parallel (i.e., `make -j`)
  mode.
* Mention that a proof contained "skip" during interactive mode, and a
  summary of skipped theorems in batch mode.  
  (#137, reported by Farah Al Wardani)
* The `types` flag when set to `on` will now print the types of
  quantified variables as well.


Bugfixes

* Automatic compilation in `Import` statements now does not clobber existing
  partial compilation results. This improves the support for multiple runs
  of Abella in parallel using the same source files.
* The *first* Type or Kind declaration was accidentally being added to
  the specification signature.  
  (Identified by Farah Al Wardani, @innofarah)
* Unification of reasoning-level formulas attempts type unification instead
  of assuming ground types.
  (#143, reported by @RandomActsOfGrammar)
* Hypothesis name hints that match generated hypothesis names should update
  the generator count.
  (#145, reported by Todd Wilson @lambdacalculator)
* Apply with unknowns now requires each computed subgoal to fully instantiate
  logic variables. ***SOUNDNESS BUG***
  (#146, reported by @Chen-PL, @jiangsy)
* Apply with unknowns now undoes variable instantiations on failed search
  for generated logic variables. ***SOUNDNESS BUG***
  (related to #146)
* Definitional clauses with higher-order parameters now trigger a
  non-well-formedness warning because they can be used to prove `false`.
  ***SOUNDNESS BUG***
  (#147, discovered by Sebastiaan Joosten, reported by Gopalan Nadathur)
* Backchaining specification clauses now respects subordination when raising
  newly introduced variables.


Changes in 2.0.7
------------------

This release adds no functionality, but fixes a number of minor bugs. It also
makes Abella compilable with OCaml versions 4.08.0 and higher.


Bugfixes

* Import statements with file paths containing . no longer break
  the HTML exporter
* Quote filenames when making shell calls  
  (#115, reported by @JimmyZJX)
* Asserting trivial facts incorrectly left variables instantiated  
  (#113, reported by Jinxu Zhao)
* Fully check that types are well-formed  
  (#128, reported by @RandomActsOfGrammar)
* Case for async object sequents should normalize before clause selection  
  (#129, reported by Guillaume Melquiond)
* Monotone for backchaining sequents should preserve backchaining  
  (Related to #129, formally justified by conjunct 2 of logic/hh_meta.thm)


Changes in 2.0.6 from 2.0.5
---------------------------

Additions

* The schematic polymorphism branch has been merged.

  You can read more about it here:

     https://abella-prover.org/schm-poly/index.html

  Thanks to Yuting Wang and Gopalan Nadathur for developing the theory
  to match the implementation by Yuting.


Tweaks to existing functionality

* Polymorphic definitions and theorems in the style of version 2.0.5
  are now recast in the style of schematic polymorphism in 2.0.6.
  There should be minimal user-visible impact.


Bugfixes

* Confusing nominal and other constants in eta-contraction
  #110 (Reported by Yuting Wang)
* Permutations of nominal constants in equivariant
  matching failed to respect types.
  #107 (Reported by Matija Pretnar)
* Error in renaming of bound variabls in metaterms.
  #106 (Reported by Yuting Wang)
* Incorrect pretty-printing of `(pi x\ p x)`.
  #104 (Reported by Dan DaCosta)


Changes in 2.0.5 from 2.0.4
---------------------------

Additions

* Added support for (first-order) polymorphic definitions. Definitions
  such as the following are now accepted.

        Define fresh : A -> B -> prop by
          nabla x, fresh x M.

  In every use of the definition, the type arguments are implicitly
  instantiated. The type-checking *for* such definitions is identical to
  taking all the unbound variable names and quantifying them on the outside.
  In other words, for the above definition, the behavior of type-checking is
  the same as if there were:

        Kind A,B  type
        Define fresh : A -> B -> prop by
          nabla x, fresh x M.

  Once such a definition is type-checked, the defined symbols are added to
  the signature as new polymorphic constants, in a vein similar to the `pi`
  constant. Whenever it is used, the type arguments are implicitly
  instantiated based on the types of the arguments.

* Added support for (first-order) polymorphic theorems. A theorem such as
  the following is now accepted.

        Theorem prune[A] : forall E L, nabla (x:A), member (E x) L ->
           exists F, E = x\ F.

  The `A` here is a type parameter, which must be distinct from the other
  basic types in scope. To use such a theorem, you *must* supply enough
  arguments. An example:

        Theorem bar : forall E G, nabla (x:tm) (y:ty),
           member (E x y) G -> exists F, E = x\ y\ F.
        intros.
        apply prune[tm] to H1.
        apply prune[ty] to H1.
        search.


Tweaks to existing functionality

* The syntax for quantifiers now allows for multiple bound variables of the
  same type. Example:

        /* Type p i -> i -> prop. */
        forall (x y : i) (f g : i -> i), p (f (g y)) (g (f x))

* The `apply` tactic now takes an optional numerical argument that defines
  the search depth for automatic searches performed for omitted arguments. A
  bound of 0 means that no searches are attempted.

* The `abbrev` and `unabbrev` tactics now both take a list of hypotheses to
  (un)abbreviate. The display of abbreviations has also been compressed.

* Error messages in interactive mode are printed to stderr in addition to any
  other output file specified with `-o`.

* The `monotone` tactic now accepts hypothesis naming hints. (#91)

Bugfixes

* Query was broken since 2.0.4-beta2.  
  (#69; reported by Ahn Ki Yung)
* Backchain now correctly takes into account inductive restrictions  
  (#70; reported by Ahn Ki Yung)
* Search now correctly raises eigenvariables over support  
  (#71; reported by Morten Rhiger)
* Undo/ProofGeneral now handles `abbrev` and `unabbrev` correctly.
* Do not normalize object sequents except when they occur shallowly
  among the assumptions or goal. Deep normalization is unsound.  
  (Reported by Dale Miller)
* The `apply` tactic was invalidly raising guessed instances over
  nominal constants that already occur in the body of the lemma.
  (#96; reported by Ahn Ki Yung and Alwen Tiu)


Changes in 2.0.4 from 2.0.3
---------------------------

Possibly breaking changes

* The `search` tactic has the same error handling behavior in interactive
  and non-interactive modes, functioning like a failed tactic in both cases
  if no subgoals were closed.
* The character `&` can no longer appear inside the names of identifiers.

Additions

* Added support for specification-level conjunction, written using `&`.

* Added a new tactic form:

        search with <witness>.

  This tactic runs the search command with a given search witness. To see
  these witnesses, run any of the other search forms with:

        Set witnesses on.

  The witness string that is printed can then be used to replay the exact
  same search. There is no backtracking involved with witness strings.
  Hence, the replay will tend to be a lot faster.

  Witnesses have the following grammar:

        witness ::= true | =
                  | left witness | right witness
                  | split(witness,witness)
                  | apply hyp
                  | intros[id1, ..., idn] witness
                  | exists[id1=term1, ..., idn=termn] witness
                  | unfold(id,n,witness1,...,witnessn)
                  | (witness)
                  | *

  The last witness form stands for a place-holder so you can give partial
  witnesses to search. In fact, the default search tactic is identical to:

        search with *.

  Please use this feature sparingly, and only when building proofs. After
  you are done with the proof, delete the "with" statements. These witnesses
  will NOT be portable across different versions of Abella, as they are very
  particular to the "search" tactic implementation.

* Added a new tactic form for `backchain` and `assert:

        backchain <num> <hyp_or_lemma>.
        assert <num> <formula>.

  where the `<num>`, which is optional, can give a depth bound to the search
  that is automatically attempted on generated goals. Give it a depth of 0
  if you want to prevent searching. The default value is the value of the
  search_depth flag.

* Added a new command line flag `-f` that takes a comma-separated list of
  key=value pairs and initializes the flags based on them. For flags that
  can be set to `on`/`off`, you can just use the key and it means to set
  them to `on`. For example, `-f subgoals=off,witnesses` sets `subgoals` to
  `off` and `witnesses` to `on`.

Tweaks to existing functionality

* Import declarations automatically compile if needed. An explicit Makefile
  is very rarely needed any more.
* The `exists` and `witness` tactics now take a comma-separated list of
  existential witnesses. Each witness can also be of the form `<id> = <term>`
  which selects a particular existential variable to instantiate. Without
  the `<id> = ` part it always instantiates the first variables.
* The `induction` tactic can now traverse an arbitrary sequence of `forall`,
  `nabla`, and `->` connectives when finding the induction argument.
* The `search` tactic now does a small amount of asynchronous reasoning
  for newly created hypotheses (e.g., reducing pattern equations).

Experimental changes (may be changed or removed in the future)

* Added limited support for predicate instantiation during import. The form

        Import "thmfile" with id1 := defid1, ..., idn := defidn.

  performs an import as usual, but any undefined predicates id in "thmfile"
  are instantiated with defined predicates defid. An undefined predicate is
  declared as usual with:

        Type id  T1 -> T2 -> ... -> Tn -> prop.

  It remains illegal to import a thm with undefined predicates without
  giving the predicate instantiations.

* Added a new "extrusive" tactic form `clear ->` that can be used to do the
  opposite of the `intros` tactic, i.e., `intros H1 ... Hn` is opposite to
  `clear -> Hn ... H1`. Variables can also be extruded in this form and they
  universally close the goal with respect to the variable if the variable is
  not free in any hypothesis.

* Extended the `subgoals` flag to take a _subgoal specification string_
  argument that can be used to fine tune the subgoals to display. As an
  example, the invocation:

        Set subgoals "0[0];1[2];2[3];3;4[10]".

  instructs Abella to show 0 additional subgoals at depth 0, max 2
  additional subgoals at 1, max 3 additional subgoals at depth 2, all
  subgoals at depth 3, and max 10 subgoals at depth 4. The depths need not
  be given in order, and any omitted depths display the default number of
  subgoals. The default flags `on`, `off`, and an _unquoted_ number have the
  following meanings:

  * `on` : the same as `"0[∞];1[∞];…"`
  * `off` : the same as `"0[0];1[0];…"`
  * `n` : the same as `"0[0];̣…;n-1[0];n[∞];n+1[0];…"`

Bugfixes

* Annotation mode (-a) output is no longer printed in other modes
* Import statements can now be undone as well from ProofGeneral
* Importing .thcs made with a different Abella binary will now print an
  error message instead of causing a segmentation fault (#39)
* Importing from different directories now works correctly
* Multiple occurrences of a single variable in a binding list is now
  correctly rejected. (#56)
* Better error messages. (#64)

New examples

* Bisimulations relating the π-calculus and the λ-calculus
  (contributed by Horace Blanc and Beniamino Accattoli)
* Type-preservation of Curry-style System F
  (contributed by Ahn Ki Yung)


Changes in 2.0.3 from 2.0.2
---------------------------

Potentially breaking changes

* Removed ~ and != notations (introduced in 2.0.2, and unused by anyone as
  far as I know). A general notation support may be considered for Abella
  in the future. Meanwhile, we prefer simplicity and predictability.


Additions

* The unfold tactic has an optional argument, "(all)", that produces a
  disjunction of all solutions to the matching problem of the conclusion of
  a subgoal and its relevant (co)definition. The disjuncts are produced in
  the same order as the clauses, but if a single clause has multiple ways to
  match the head then the disjuncts for that clause are in some unspecified
  order (that depends on the details of the unification algorithm).
* The following tactic forms have been added:

      apply *H to ...
      apply ... to ... *H ...
      backchain *H
      cut *H ...
      cut ... with *H
      inst *H with ...
      monotone *H with ...

  In each case, if H names a hypothesis, then the tactic consumes the
  hypothesis (like the clear tactic). Note that if hypothesis hints are
  given, then these hints are used *after* consuming the hypotheses. Thus,
  if one writes:

      foo : apply lem to *foo bar baz.

  then the hypothesis named foo is effectively *replaced* with a new
  hypothesis named foo that is the result of applying the lem to the old foo
  and the other arguments.
* Optional semi-colon allowed before the first clause in a definition or
  co-definition block.
* Variable renaming can overwrite old variables that have already been
  instantiated.
* The clear tactic can also remove instantiated variables.
* The settable option "types" displays the types of variables in subgoals

Internal changes

* The parser has stronger checks to enforce the lexical convention that all
  identifiers matching n[0-9]+ are nominal constants.
* Most user-visible error messages have been made a bit more precise and
  informative.

Bugfixes

* Abella now builds on versions of OCaml between 3.12.1 and 4.01.0
  (inclusive) again.
* Unfolding named clauses now raises clauses over the support of the goal
  and existentially closes over residual logic variables (soundness bug
  introduced in 2.0.2) (#33)
* Unfolding named clauses whose heads do not unify with goal now causes
  failure instead of success. (soundness bug introduced in 2.0.2)
* Web-page generating scripts properly handle proof syntax changes since
  version 1.3.5.
* The toplevel now prints tactics using the same syntax as in proof scripts.
* The apply tactic can now apply lemmas that do not have a forall prefix.
* In the Query command, fresh logic variables are allocated to be
  independent of existing capitalized identifiers in the query. This
  prevents the generated solutions from appearing to be non-idempotent.

New examples

* The process calculus examples have been re-organized. There are now two
  medium sized new developments of the meta-theory of bisimulation-up-to
  techniques for CCS and the pi-calculus.


Changes in 2.0.2 from 2.0.1
---------------------------

Potentially breaking changes.

* Constants with names matching n[0-9]+ are forcibly treated as nominal
  constants. This fixes a unsoundness due to ambiguous parsing of such
  constants in proofs.
* The tactic "exists" now has a synonym: "witness". This adds "witness" to
  the list of keywords.

Additions

* Specification language now supports <= in addition to =>
* Binders are printed using variable naming hints from the source instead of
  in a normalized form (x1, x2, etc.)
* Can unfold the nth clause of an inductive or co-inductive
  definition block using "unfold n".
* Can name clauses in the specification (in .mod files) using a comment of
  the form %:nm: right before a clause. There must be a single Abella
  identifier and no spaces between the two :s.
* Can unfold a specific clause named "nm" of a specification using "unfold
  nm".
* New flag "instantiations" shows variable instantiations at the top of a
  subgoal.
* New notation "~ F" for "F -> false".
* The backchain tactic now allows backchaining formulas that are not
  prenex-quantified implications. The "head" of the backchained formula is
  interpreted as any formula that is not an implication.
* The rename tactic has been extended to also allow renaming variables, with
  an identical syntax.

Internal changes

* Terms and meta-terms now have pretty-printer with a plugin architecture
  for future extensions.

Bug fixes

* The exists/witness tactics now rename to avoid capture (#22)
* Raising over nominal constants in spec. sequents raises over the support
  of the whole sequent rather than just its conclusion.
* Normalizing of binders now avoid capture (#23)
* Instantiated variables are no longer printed in the variables list of a
  sequent.
* Higher-order definitions have a stricter stratification check that
  complains both about actual and potential unsound definitions.
* The subordination checker now does not complain about invalid subterms for
  types that have not been explicitly Closed.
* The rename tactic cannot rename lemmas (i.e., theorems proved earlier)

New examples

* Formalization of the meta-theory of higher-order HH using only the
  reasoning logic of Abella (examples/logic/hh_meta.thm).


<!-- Local Variables: -->
<!-- mode: markdown -->
<!-- fill-column: 76 -->
<!-- End: -->
