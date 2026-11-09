Reasoning-Level Modules
=======================

Abella supports reasoning-level modules in `.thmod` files and inline
in `.thm` files. A module declares a parameterized namespace of kinds,
constants, predicates, definitions, and theorems:

```text
Module List[T].
  Kind lst type.
  Type lnil lst.
  Type lcons T -> lst -> lst.
  Type contains T -> lst -> prop.
  Axiom head : forall (x:T) (xs:lst), contains x (lcons x xs).
End List.
```

The top-level module name must match the file basename. Nested modules
use the same `Module`/`End` form and may have their own type parameters.
Module parameters are schematic type variables and are not exported as
items; internal `Kind` types are generative and fresh in every instance.

A `.thm` file, or interactive input, may also define modules directly.
Such modules are local to that file or session and are not exported by
the `.thc` artifact:

```text
Module Counter.
  Kind counter type.
  Type zero counter.
  Type succ counter -> counter.
  Type positive counter -> prop.
  Axiom one_pos : positive (succ zero).
End Counter.
```

Use `Show Module` to print a module summary:

```text
Show Module Counter.
Show Module C.
Show Module "List".
```

The first form shows an in-scope module, the second an imported
instance, and the third a module loaded from a `.thmod` file. The
summary prints kinds, types, definitions, axioms, and theorem
statements without proofs.

A `.thm` file imports a reasoning module with `Import Module`:

```text
Kind nat type.
Import Module L = "List"[nat].
Import Module L2 = "List"[bool].
```

A quoted target names a `.thmod` file without its extension. A type
argument list is required for a parameterized template, in the order of
its parameters. An alias changes only the import prefix; it does not
change the target's keys. Items are then available as `L.contains`,
`L.lcons`, and so on.

An unquoted target names a nested module or an existing instance in
scope. An instance is already instantiated; supplying brackets to it is
an error.

A `with` clause maps declared predicates and axiom items:

```text
Import Module E = "Eq"[nat] with
  eq := nat_eq,
  refl := nat_eq_refl.
```

Mapped predicates are removed and their values are not re-exported.
Mapped axioms become aliases carrying the value's tag. Unmapped
declared predicates and axioms remain as keys and may be mapped by a
later aliased re-import. Key names are relative to the target, including
dotted names for modules the target imported.

The same module can be instantiated multiple times. Each instance gets
distinct internal `Kind` types, while parameter occurrences are replaced
by the supplied type arguments. Compiled artifacts are written to
`.thmodc`; `-c` selects a different output path.

Inside a module, `Specification`, ordinary `Import`, `Close`, `Suspend`,
`Quit`, and `Abort` are not allowed. Declared predicates may not have
`prop` in an argument position, and stratification findings are hard
errors. A `.thmod` may not use specification-logic sequents (`{ ... }`);
a module defined inline in a `.thm` may use them.

Reasoning-module examples
=========================

Positive examples:

- `List.thmod` and `ListUse.thm`: a parameterized list theory imported
  at two element types.
- `Box.thmod` and `BoxUse.thmod`: two instances of a module with an
  internal `Kind`, showing distinct internal types.
- `Nested.thmod` and `NestedUse.thmod`: a nested parameterized module.
- `Eq.thmod`, `EqUse.thmod`, and `EqUseDecl.thmod`: an abstract
  predicate and axiom mapped to defined and declared predicates and
  theorems/axioms.
- `PropKey.thmod` and `PropKeyUse.thmod`: zero-argument predicate keys.
- `Keys.thmod` and `KeysUse.thmod`: unmapped keys and an aliased
  re-import.
- `ShowModule.thm`: inline and imported module summaries, plus a
  summary loaded from a `.thmod` file.
- `test/modules/EdgeClosed.thm`: a closed-type subordination failure
  during an import of an inline module.

`test/modules/errors/` contains examples that should fail: higher-order
declared predicates, polymorphic value mismatch, unfinished axiom
values, internal-type keys, and axiom statement mismatches.

Run everything from the repository root:

```sh
bash examples/modules/run.sh _build/default/bin/abella.exe
```

The script compiles dependencies in order, checks the expected errors,
and leaves `.thmodc`/`.thc` files in `_build`.
