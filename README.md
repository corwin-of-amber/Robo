# Robo / Scribble

A game for learning Lean 4 in which a cute little smart-elf joins you on your exploration of a universe inhabited by formalosophers. You can play the game on the [Lean Game Server](https://adam.math.hhu.de/).

The game is currently available in two languages.  In German, the game and its smart-elf are called *Robo*, in English, *Scribble*.  We are actively looking for translations into other languages, see [Translations](#translations) below.

## Game content

| Planet     | key mathematical content           | Lean tactics introduced               | Boss level                                                         |
|:---------- |:---------------------------------- | ------------------------------------- | ------------------------------------------------------------------ |
| Logo       | propositional logic: ∧, ∨, ¬       | `rfl`, `left`, `right`,`tauto`, …     | –                                                                  |
| Implis     | propositional logic: ⇒, ⇔          | `apply`, `intro`, `revert`, `rw`, …   | A ⇒ B equivalent to ¬ A ∨ B                                        |
| Saturn     | elementary arithmetic, polynomials | `ring`, `rw` for equations            | a well-known polynomial sums-of-squares formula                    |
| Quantus    | predicate logic, even/odd numbers  | `use`, `obtain`, `decide`, `push_neg` | [Drinker's paradox](https://en.wikipedia.org/wiki/Drinker_paradox) |
| Luna       | inequalities                       | `linarith`, `omega`                   | –                                                                  |
| Spinoza    | proof structuring                  | `suffices`, `by_contra`, `contrapose` | –                                                                  |
| Babylon    | ∑ notation, induction              | `induction'`                          | sum of cubes                                                       |
| Piazza     | basic set theory                   | `ext`, `simp`                         | –                                                                  |
| Prado      | prime numbers                      | –                                     | exactly one even prime                                             |
| Euklid     | ∏ notation                         | –                                     | infinitely many primes                                             |
| Vieta      | maps (between types)               | `funext`                              | another induction exercise                                         |
| Epo        | surjective maps, axiom of choice   | `choose`                              | map surjective ⇔ has right inverse                                 |
| Mono       | injective maps                     | –                                     | map injective ⇔ has left inverse                                   |
| Iso        | bijective maps                     | –                                     | map bijective ⇔ has inverse                                        |
| Samarkand  | (pre)images of subsets             | –                                     | map surjective ⇔ induced contravariant map on powersets injective  |
| Cantor     | fixed points of maps               | –                                     | ℕ-valued sequences uncountable                                     |
| Robotswana (Ethiopia) | matrices, trace                    | –                                     | characterization of trace map                                      |
| Ciao       | (good-bye planet)                  | –                                     | –                                                                  |


# Contribution

## Bugs

For small content fixes like spelling mistakes, missing hints, missing documentation, or other things that were unclear or you've struggled with, please open an issue or PR here!

Issues concerning the underlying software are better placed in the [lean4game repo](https://github.com/leanprover-community/lean4game).

## Translations

Please contact [me](https://www.math.uni-duesseldorf.de/~zibrowius/) if you are willing to help translate the game into other languages!  The process is explained in our  [Translation Guide](./docs/TranslationGuide.md).

## New Content

Contributions of new planets are welcome! Each planet in the game talks about a new topic
in a standard mathematics undergrad (bachelor) curriculum at university.

Please follow our [Contribution Guide](./docs/ContributionGuide.md),
 which helps you create new content step-by-step.

# Technical

## Building

This checkout uses `leanprover/lean4:v4.36.0-rc2` from `lean-toolchain`.
With elan installed, build the game from the repository root:

```sh
python3 scripts/check-dependencies.py
lake build
```

The committed `lake-manifest.json` fixes the complete dependency graph. Qq and
Batteries use 4.36.0-rc2; GameServer and i18n use the tested 4.35 releases.
This game does not require a mathlib cache download.

`package-overrides.json` records the revisions needed when preparing a Wasm
build. Before invoking Lean's `crazy/builder.ts`, fetch those dependencies with
native Lake:

```sh
lake build --packages=package-overrides.json --no-build || test "$?" -eq 3
```

Lake's status 3 means compilation is required, which is expected at this step.
The Wasm builder copies the dependencies into its guest filesystem and converts
the resolved graph to local paths, so the guest does not fetch packages.

## Updating the toolchain or dependencies

Update `lean-toolchain` and the GameServer revision in `lakefile.lean` together.
Qq follows the selected Lean version. Review the dependency graph after
`lake update -R`: inherited dependencies can still select older versions.
Align `package-overrides.json` with the intended revisions in the regenerated
`lake-manifest.json`, then run the consistency check and rebuild natively and
with Wasm Lake. Commit both configuration files with the toolchain update.
The check compares exact revisions and does not replace either build.

The declarations in `lakefile.lean`, resolved lockfile, and Wasm overrides have
different roles; keep all three. Updating dependencies is an intentional change
to the locked graph, rather than a routine prerequisite for every build.

## Refactoring existing worlds

The bash script `sofi.sh` (`s`ort `o`ut `f`ilenames and `i`mports), contained in the root folder,
can help restructure existing worlds, see the
 [documentation](https://github.com/leanprover-community/lean4game/blob/main/doc/create_game.md#5-refactoring-an-existing-world).

# Technical support

In case of issues with our server at `adam.math.hhu.de`, please send an email to <a href="mailto:matvey.lorkish@hhu.de?subject=Lean4Game: <Your%20Question>">this address</a>.  

