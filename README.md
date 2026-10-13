# Artifact for _Trees, Walks, and Words: A Logic for File System Interactions_

- Artifact: [DOI / Zenodo](https://doi.org/10.5281/zenodo.23215901), [GitHub](https://github.com/atlas-brown/twe-artifact)
- Paper: [link](https://atlas.cs.brown.edu/pdf/accordion:popl:2027.pdf), [HotCRP #505](https://popl27.hotcrp.com/paper/505)
- License: MIT
- Badges sought: **Functional**, **Reusable**

This is a [Lean 4](https://lean-lang.org/) mechanization of the paper's formal development, including all major theorems, excluding complexity bounds.
The artifact is ~20,600 lines of Lean.
Checking it takes a few minutes after dependencies are downloaded.

This README contains instructions for an artifact reviewer to check the mechanization for functionality and reusability.
Reviewers should:

1. Set up the project and check proofs ([Milestone 1: Kick the Tires](#milestone-1-getting-started-kick-the-tires), <30 minutes)
2. Evaluate that the claims of the artifact match the paper ([Milestone 2: Functional](#milestone-2-evaluating-the-claims-functional), <2 hours)
3. Evaluate reusability of the mechanization ([Milestone 3: Reusable](#milestone-3-reusing-the-artifact-reusable), <15 minutes).

## Contents

1. [List of claims](#list-of-claims)
2. [Representation decisions](#representation-decisions)
3. [Milestone 1: Getting started (Kick the Tires)](#milestone-1-getting-started-kick-the-tires)
4. [Milestone 2: Evaluating the claims (Functional)](#milestone-2-evaluating-the-claims-functional)
5. [Milestone 3: Reusing the artifact (Reusable)](#milestone-3-reusing-the-artifact-reusable)

## List of claims

The claims of the paper are listed below alongside the sources of their Lean formalizations.
These lists include all the definitions and theorems of the paper, excluding complexity claims (see [Not claimed](#not-claimed)).
They will be verified to match the paper under [Milestone 2: Functional](#milestone-2-evaluating-the-claims-functional).

1. [WhileFS and its symbolic semantics](#whilefs-and-its-symbolic-semantics), verified in [Step 2](#step-2-whilefs-and-its-symbolic-semantics)
2. [Hardness of TWE](#hardness-of-twe), verified in [Step 3](#step-3-hardness-of-twe)
3. [Decidability of linear TWE](#decidability-of-linear-twe), verified in [Step 4](#step-4-decidability-of-linear-twe)
4. [Decidability of bounded TWE](#decidability-of-bounded-twe), verified in [Step 5](#step-5-decidability-of-bounded-twe)
5. [Notation](#notation)
6. [Not claimed](#not-claimed)

Note that all file paths are relative to `Accordion/`.
The tables of this section give Lean names relative to the namespace `Accordion`; the tables and statements of [Milestone 2](#milestone-2-evaluating-the-claims-functional) give them in full.

### WhileFS and its symbolic semantics

Definitions:

| Paper                                               | Section/Figure | Lean                                                                                           | File                                                                                                               |
| --------------------------------------------------- | -------------- | ---------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------ |
| Paths and components                                | Fig. 2         | `Path`, `Component`                                                                            | [`Path.lean:7`](Accordion/Path.lean#L7)                                                                            |
| WhileFS syntax                                      | Fig. 2         | `Val`, `Expr`, `Command`                                                                       | [`WhileFS.lean:26`](Accordion/WhileFS.lean#L26)                                                                    |
| File trees, one-holed contexts, path resolution     | Fig. 3         | `FileTree`, `FileTree.Ctx`, `FileTree.Focus`, `FileTree.resolve`                               | [`FileTree.lean:11`](Accordion/FileTree.lean#L11), [`FileTree/Zipper.lean:67`](Accordion/FileTree/Zipper.lean#L67) |
| Concrete operational semantics of WhileFS           | Fig. 4         | `Eval`, `Step`, `Multistep`                                                                    | [`WhileFS.lean:83`](Accordion/WhileFS.lean#L83)                                                                    |
| TWE                                                 | Fig. 5         | `TWE.Path`, `TWE.Tree`, `TWE.Set`, `TWE.Atom`, `TWE.Formula`, `TWE.Model`, `TWE.Model.satAtom` | [`TWE.lean:72`](Accordion/TWE.lean#L72), [`Formula.lean:10`](Accordion/Formula.lean#L10)                           |
| Symbolic operational semantics of WhileFS           | Fig. 6         | `SEval`, `SStep`, `SMultistep`, `SState.instantiate`                                           | [`WhileFS/Symbolic.lean:111`](Accordion/WhileFS/Symbolic.lean#L111)                                                |

Theorems:

| Paper                                        | Section/Figure  | Lean                                   | File                                                                                |
| -------------------------------------------- | --------------- | -------------------------------------- | ----------------------------------------------------------------------------------- |
| Soundness                                    | §4.2, theorem 1 | `WhileFS.Symbolic.soundness`           | [`WhileFS/Symbolic/Adequacy.lean:14`](Accordion/WhileFS/Symbolic/Adequacy.lean#L14) |
| Completeness                                 | §4.2, theorem 1 | `WhileFS.Symbolic.completeness`        | [`WhileFS/Symbolic/Adequacy.lean:22`](Accordion/WhileFS/Symbolic/Adequacy.lean#L22) |

### Hardness of TWE

Definitions:

| Paper                                               | Section/Figure | Lean                                                                                           | File                                                                                                               |
| --------------------------------------------------- | -------------- | ---------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------ |
| WE                                                  | §5             | `WE.Formula`                                                                                   | [`WE.lean:48`](Accordion/WE.lean#L48)                                                                              |
| WE + LEN                                            | §5             | `WE.Len.Formula`                                                                               | [`WE/Len.lean:29`](Accordion/WE/Len.lean#L29)                                                                      |
| WE + NORM                                           | §5.1           | `WE.Norm.Formula`                                                                              | [`WE/Norm.lean:30`](Accordion/WE/Norm.lean#L30)                                                                    |
| WE + WALK                                           | §5.1           | `WE.Walk.Formula`                                                                              | [`WE/Walk.lean:34`](Accordion/WE/Walk.lean#L34)                                                                    |
| WE + SHAPE + REG                                    | §5.2           | `WE.ShapeReg.Formula`                                                                          | [`WE/ShapeReg.lean:57`](Accordion/WE/ShapeReg.lean#L57)                                                            |
| Reduction from WE + LEN to WE + NORM                | §5.1           | `WE.Len.Formula.toNorm`                                                                        | [`WE/Len/ToNorm.lean:18`](Accordion/WE/Len/ToNorm.lean#L18)                                                        |
| Reduction from WE + LEN to WE + WALK                | §5.1           | `WE.Len.Formula.toWalk`                                                                        | [`WE/Len/ToWalk.lean:18`](Accordion/WE/Len/ToWalk.lean#L18)                                                        |
| Reduction from WE + LEN to WE + SHAPE + REG         | §5.2           | `WE.Len.Formula.toShapeReg`                                                                    | [`WE/Len/ToShapeReg.lean:18`](Accordion/WE/Len/ToShapeReg.lean#L18)                                                |
| Reduction from WE + LEN to TWE                      | §5             | `WE.Len.Formula.toTWE`                                                                         | [`WE/Len/ToTWE.lean:20`](Accordion/WE/Len/ToTWE.lean#L20)                                                          |

Theorems:

| Paper                                        | Section/Figure  | Lean                                   | File                                                                                |
| -------------------------------------------- | --------------- | -------------------------------------- | ----------------------------------------------------------------------------------- |
| WE + LEN reduces to WE + NORM                | §5.1, theorem 2 | `WE.Len.toNorm_equisat`                | [`TWE/Hardness.lean:18`](Accordion/TWE/Hardness.lean#L18)                           |
| WE + LEN reduces to WE + WALK                | §5.1, theorem 3 | `WE.Len.toWalk_equisat`                | [`TWE/Hardness.lean:23`](Accordion/TWE/Hardness.lean#L23)                           |
| WE + LEN reduces to WE + SHAPE + REG         | §5.2            | `WE.Len.toShapeReg_equisat`            | [`TWE/Hardness.lean:29`](Accordion/TWE/Hardness.lean#L29)                           |
| WE + LEN reduces to TWE                      | §5              | `WE.Len.toTWE_equisat`                 | [`TWE/Hardness.lean:35`](Accordion/TWE/Hardness.lean#L35)                           |
| WE + LEN reduces to TWE through WE + NORM    | §5              | `WE.Len.toTWE_toNorm_equisat`          | [`TWE/Hardness.lean:40`](Accordion/TWE/Hardness.lean#L40)                           |
| WE + LEN reduces to TWE through WE + WALK    | §5              | `WE.Len.toTWE_toWalk_equisat`          | [`TWE/Hardness.lean:45`](Accordion/TWE/Hardness.lean#L45)                           |

### Decidability of linear TWE

Definitions:

| Paper                                               | Section/Figure | Lean                                                                                           | File                                                                                                               |
| --------------------------------------------------- | -------------- | ---------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------ |
| Linear TWE                                          | §6.1           | `TWE.Linear.Model`, `TWE.Linear.Formula.SAT`                                                   | [`TWE/Linear.lean:43`](Accordion/TWE/Linear.lean#L43), [`TWE/Linear.lean:50`](Accordion/TWE/Linear.lean#L50)       |
| Reduction from linear TWE to WE                     | §6.1           | `TWE.Linear.Formula.toWE`                                                                      | [`TWE/Linear/ToWE.lean:133`](Accordion/TWE/Linear/ToWE.lean#L133)                                                  |

Theorems:

| Paper                                        | Section/Figure  | Lean                                   | File                                                                                |
| -------------------------------------------- | --------------- | -------------------------------------- | ----------------------------------------------------------------------------------- |
| Linear TWE reduces to WE                     | §6.1, theorem 4 | `TWE.Linear.toWE_equisat`              | [`TWE/Decidability.lean:19`](Accordion/TWE/Decidability.lean#L19)                   |
| WE is decidable    | cited in §6.1   | `WE.Formula.sat?_iff`, `DecidablePred WE.Formula.SAT` | [`WE/Decidability.lean:16`](Accordion/WE/Decidability.lean#L16), [`:21`](Accordion/WE/Decidability.lean#L21) |
| Linear TWE is decidable                      | §6.1, corollary 1 | `TWE.Linear.sat?_iff`, `DecidablePred TWE.Linear.Formula.SAT` | [`TWE/Decidability.lean:28`](Accordion/TWE/Decidability.lean#L28), [`:33`](Accordion/TWE/Decidability.lean#L33) |

### Decidability of bounded TWE

Definitions:

| Paper                                               | Section/Figure | Lean                                                                                           | File                                                                                                               |
| --------------------------------------------------- | -------------- | ---------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------ |
| Bounded TWE                                         | §6.2           | `TWE.Bounded.Model`, `TWE.Bounded.Formula.SAT`                                                 | [`TWE/Bounded.lean:25`](Accordion/TWE/Bounded.lean#L25), [`TWE/Bounded.lean:32`](Accordion/TWE/Bounded.lean#L32)   |
| Reduction from bounded non-linear TWE to linear TWE | §6.2           | `TWE.Bounded.Formula.toLinear`                                                                 | [`TWE/Bounded/ToLinear.lean:19`](Accordion/TWE/Bounded/ToLinear.lean#L19)                                          |
| Reduction from bounded non-linear TWE to WE         | §6.2           | `TWE.Bounded.Formula.toWE`                                                                     | [`TWE/Bounded/ToWE.lean:18`](Accordion/TWE/Bounded/ToWE.lean#L18)                                                  |

Theorems:

| Paper                                        | Section/Figure  | Lean                                   | File                                                                                |
| -------------------------------------------- | --------------- | -------------------------------------- | ----------------------------------------------------------------------------------- |
| Bounded TWE reduces to linear TWE            | §6.2, theorem 5 | `TWE.Bounded.toLinear_equisat`         | [`TWE/Decidability.lean:41`](Accordion/TWE/Decidability.lean#L41)                   |
| Bounded TWE reduces to WE                    | §6.2, theorem 5 | `TWE.Bounded.toWE_equisat`             | [`TWE/Decidability.lean:46`](Accordion/TWE/Decidability.lean#L46)                   |
| Bounded TWE is decidable                     | §6.2, corollary 2 | `TWE.Bounded.sat?_iff`, `DecidablePred (TWE.Bounded.Formula.SAT k)` | [`TWE/Decidability.lean:55`](Accordion/TWE/Decidability.lean#L55), [`:61`](Accordion/TWE/Decidability.lean#L61) |

The artifact does not prove space complexity bounds for reductions (see [Not claimed](#not-claimed)).

### Notation

| Paper                         | Section/Figure | Lean                             | File                                                                                        |
| ----------------------------- | -------------- | -------------------------------- | ------------------------------------------------------------------------------------------- |
| ε                             | Fig. 2         | `ε`                              | [`Path.lean:86`](Accordion/Path.lean#L86)                                                   |
| p/q                           | Fig. 2         | `p / c`                          | [`Path.lean:80`](Accordion/Path.lean#L80)                                                   |
| join p₁ p₂                    | Fig. 4         | `p ++ q`                         | [`Path.lean:81`](Accordion/Path.lean#L81)                                                   |
| ϵ, ., ..                      | Fig. 2         | `ϵ`, `∙`, `‥`                    | [`Path.lean:83`](Accordion/Path.lean#L83)                                                   |
| ⊤, ⊥, Φ ∧ Ψ, Φ ∨ Ψ, ¬Φ        | §4.1           | `⊤`, `⊥`, `φ ⋏ ψ`, `φ ⋎ ψ`, `∼φ` | [`Formula.lean:21`](Accordion/Formula.lean#L21)                                             |
| ⟨σ, θ⟩ ⊨ Φ                    | Fig. 5         | `m ⊨ φ`                          | [`Formula.lean:63`](Accordion/Formula.lean#L63)                                             |
| P · Q                         | Fig. 5         | `p ++ q`                         | [`TWE.lean:130`](Accordion/TWE.lean#L130)                                                   |
| P = Q, IsLin P                | Fig. 5         | `p ≐ q`, `Lin p`                 | [`TWE.lean:171`](Accordion/TWE.lean#L171)                                                   |
| S = S′                        | Fig. 5         | `s ≐ s'`                         | [`TWE.lean:175`](Accordion/TWE.lean#L175)                                                   |
| P ↠<sub>T</sub> L             | Fig. 5         | `τ ⊢ p ⇝ l`                      | [`TWE.lean:173`](Accordion/TWE.lean#L173)                                                   |
| T ∈ H, A ∈ S                  | Fig. 5         | `τ ∶ h`, `a ∈̇ s`                 | [`TWE.lean:174`](Accordion/TWE.lean#L174)                                                   |
| T[L]                          | Fig. 5         | `τ[l]`                           | [`TWE.lean:133`](Accordion/TWE.lean#L133)                                                   |
| T[L ↦ T′]                     | Fig. 5         | `τ[l ↦ τ']`                      | [`TWE.lean:138`](Accordion/TWE.lean#L138)                                                   |
| U = V                         | §5             | `u ≐ v`                          | [`WE.lean:51`](Accordion/WE.lean#L51)                                                       |
| e ⇓<sup>ρ</sup> v             | Fig. 4         | `e ⇓[ρ] v`                       | [`WhileFS.lean:140`](Accordion/WhileFS.lean#L140)                                           |
| (c, ς) ⟶<sup>1</sup> (c′, ς′) | Fig. 4         | `(c, ς) ⟶ (c', ς')`              | [`WhileFS.lean:265`](Accordion/WhileFS.lean#L265)                                           |
| (c, ς) ⟶<sup>\*</sup> (c′, ς′)           | §3.3           | `(c, ς) ⟶* (c', ς')`             | [`WhileFS.lean:280`](Accordion/WhileFS.lean#L280)                                           |
| e evaluates to v̂ under ρ̂, generating Φ | Fig. 6 | `e ⇓[ρ] v ∣ Φ`                   | [`WhileFS/Symbolic.lean:170`](Accordion/WhileFS/Symbolic.lean#L170)                         |
| (c, ς̂) ⟶<sup>1</sup> (c′, ς̂′) | Fig. 6         | `(c, sς) ⇝ (c', sς')`            | [`WhileFS/Symbolic.lean:310`](Accordion/WhileFS/Symbolic.lean#L310)                         |
| (c, ς̂) ⟶<sup>\*</sup> (c′, ς̂′)           | §4.2           | `(c, sς) ⇝* (c', sς')`           | [`WhileFS/Symbolic.lean:325`](Accordion/WhileFS/Symbolic.lean#L325)                         |
| ⟦⟨ρ̂, T, π̂⟩⟧<sub>σ,θ</sub>     | §4.2           | `⟦sς⟧ m`                         | [`WhileFS/Symbolic.lean:109`](Accordion/WhileFS/Symbolic.lean#L109)                         |

### Not claimed

Though the constructions should be PSPACE, the artifact does not formally state nor prove time or space complexity bounds.

## Representation decisions

The mechanization makes the following representation decisions:

-   Due to Lean kernel restrictions on nested inductive types, directory entries, which are finite maps from names to file trees in the paper, are modeled as sorted lists (see `FileTree.Entries`, [`FileTree/Entries.lean:9`](Accordion/FileTree/Entries.lean#L9)).
    Subsequent definitions and theorems require the instance arguments `[Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]`, and hold for every order on names that satisfies those laws.

-   Well-formedness of models and definedness of instantiation, which the paper leaves implicit, are explicit hypotheses.
    `TWE.Model.WF` ([`TWE.lean:297`](Accordion/TWE.lean#L297)) requires that every location variable denotes a linear path and that every tree variable denotes a tree with sorted entries.
    The instantiation of a symbolic state is partial (`⟦sς⟧ m = some ς`).
    `m ⊫ sς` (`SState.Sat`, [`WhileFS/Symbolic.lean:335`](Accordion/WhileFS/Symbolic.lean#L335)) states that `m` satisfies the path condition of `sς` and that every value in the store of `sς` instantiates under `m` (`SStore.Valid`, [`WhileFS/Symbolic.lean:329`](Accordion/WhileFS/Symbolic.lean#L329)).

-   Nondeterministic reductions are modeled as functions to guesses: a `Guess α` is a nondeterministic computation that produces one `α` per run (see `Guess`, [`Guess.lean:9`](Accordion/Guess.lean#L9)).
    `x ∈ D` states that `x` is the result of some run (see `Guess.Mem`, [`Guess.lean:21`](Accordion/Guess.lean#L21)).

-   The supply of variables is usually assumed to be infinite using instance arguments `[TWE.Vars.Unbounded V]` ([`TWE/Fresh.lean:21`](Accordion/TWE/Fresh.lean#L21)).
    The introduction of fresh variables is modeled as the choice of a variable outside some finite set of existing variables (see `TWE.Vars.Fresh`, [`TWE/Fresh.lean:28`](Accordion/TWE/Fresh.lean#L28)).

-   Likewise, the alphabet of names is also infinite and modeled by instance arguments `[Infinite Γ]`.

-   The reductions from WE + LEN to TWE fragments use a marker letter; the mechanization takes the default letter of the alphabet, given by the instance argument `[Inhabited Γ]` (see `WE.Len.Formula.toNorm`, [`WE/Len/ToNorm.lean:18`](Accordion/WE/Len/ToNorm.lean#L18)).

-   The reduction to WE + SHAPE + REG separates the letters of a word by a separator letter outside the source alphabet, so that no word of a source model contains it.
    Its target alphabet adds that letter to `Γ` (see `WE.LenEq.ToShapeReg.Alphabet`, [`WE/LenEq/ToShapeReg/Defs.lean:29`](Accordion/WE/LenEq/ToShapeReg/Defs.lean#L29)).

-   Decidable equality of names and variables is implicit in the paper and modeled by instance arguments `[DecidableEq Γ]`, `[DecidableEq X]` and `[TWE.Vars.Comparable V]` (see `TWE.Vars.Comparable`, [`TWE/Fresh.lean:13`](Accordion/TWE/Fresh.lean#L13)).

-   A single version of WE with both letter and word variables (see `WE.Vars`, [`WE.lean:24`](Accordion/WE.lean#L24)) is used for all results.
    The reductions from WE + LEN first replace each letter variable by a word variable of length one (see `WE.Len.ToLenEq.guards`, [`WE/Len/ToLenEq/Defs.lean:36`](Accordion/WE/Len/ToLenEq/Defs.lean#L36)).

## Milestone 1: Getting started (Kick the Tires)

This phase should take under 30 minutes, almost all of it download time.

### a. Requirements

- Linux, macOS or Windows (tested on x86-64 Linux).

- `git` and `curl`.

- [elan](https://github.com/leanprover/elan) (tested with 4.2.3)

- ~10 GB of free disk space, mostly for mathlib.

- Network access for the installation steps below, after which nothing is downloaded.

### b. Installation

1.  [Install elan](https://github.com/leanprover/elan#installation), the Lean toolchain manager, if it is not already installed, and add `lake` to the `PATH` of the current shell.
    On Linux/macOS:

    ```sh
    curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
    ```

    On Windows:

    ```sh
    curl -O --location https://elan.lean-lang.org/elan-init.ps1
    powershell -ExecutionPolicy Bypass -f elan-init.ps1
    del elan-init.ps1
    ```

2.  Download and unpack the [artifact](https://doi.org/10.5281/zenodo.23215901).
    Enter its root directory, which contains [`lakefile.toml`](lakefile.toml).
    _All subsequent commands are run from that directory._

3.  Fetch dependencies, including mathlib, and its prebuilt object files:

    ```sh
    lake exe cache get
    ```

### c. Sanity test

Build the project to check every definition and proof.

**Run:**

```sh
lake build --wfail
```

This should take one or two minutes and produce successful output ending with the following or similar:

```
✔ [1118/1120] Built Accordion.TWE.Decidability (586ms)
✔ [1119/1120] Built Accordion (636ms)
Build completed successfully (1120 jobs).
```

No line of the output should contain `warning` or `error`.

## Milestone 2: Evaluating the claims (Functional)

A successful build shows that the proofs check.
In this part, reviewers should confirm that the definitions and theorems in the paper match the artifact:

1.  All axioms are standard ([Step 1](#step-1-axioms))
2.  WhileFS and its symbolic semantics ([Step 2](#step-2-whilefs-and-its-symbolic-semantics))
3.  Hardness of TWE ([Step 3](#step-3-hardness-of-twe))
4.  Decidability of linear TWE ([Step 4](#step-4-decidability-of-linear-twe))
5.  Decidability of bounded TWE ([Step 5](#step-5-decidability-of-bounded-twe))

In steps 2 to 5, verify that the mechanized definitions and theorem statements match the paper by reviewing the sources and signatures below.
Note the [Representation decisions](#representation-decisions).

### Step 1: Axioms

[`Axioms.lean`](Axioms.lean) holds one `#print axioms` command for each named theorem of the [list of claims](#list-of-claims), in the order of the list.
The three `DecidablePred` instances are anonymous and follow from the `sat?_iff` theorems listed with them.
`#print axioms` follows every dependency of a theorem and prints the axioms used.

Checking it should show only the following standard axioms:

-   `propext`, propositional extensionality
-   `Classical.choice`, choice
-   `Quot.sound`, quotient soundness

**Run:**

```sh
lake env lean Axioms.lean
```

It should produce the following output:

```
'Accordion.WhileFS.Symbolic.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.WhileFS.Symbolic.completeness' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.WE.Len.toNorm_equisat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.WE.Len.toWalk_equisat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.WE.Len.toShapeReg_equisat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.WE.Len.toTWE_equisat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.WE.Len.toTWE_toNorm_equisat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.WE.Len.toTWE_toWalk_equisat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.TWE.Linear.toWE_equisat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.WE.Formula.sat?_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.TWE.Linear.sat?_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.TWE.Bounded.toLinear_equisat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.TWE.Bounded.toWE_equisat' depends on axioms: [propext, Classical.choice, Quot.sound]
'Accordion.TWE.Bounded.sat?_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Step 2: WhileFS and its symbolic semantics

#### 2A. Paths and components

| Paper       | Section/Figure | Lean                    | File                                      |
| ----------- | -------------- | ----------------------- | ----------------------------------------- |
| Component q | Fig. 2         | `Accordion.Component`   | [`Path.lean:7`](Accordion/Path.lean#L7)   |
| Path p      | Fig. 2         | `Accordion.Path`        | [`Path.lean:15`](Accordion/Path.lean#L15) |
| join p₁ p₂  | Fig. 4         | `Accordion.Path.join`   | [`Path.lean:27`](Accordion/Path.lean#L27) |
| base p      | Fig. 4         | `Accordion.Path.base`   | [`Path.lean:32`](Accordion/Path.lean#L32) |
| dir p       | Fig. 4         | `Accordion.Path.dir`    | [`Path.lean:37`](Accordion/Path.lean#L37) |
| norm p      | Fig. 4         | `Accordion.Path.norm`   | [`Path.lean:46`](Accordion/Path.lean#L46) |
| p lin       | Fig. 5         | `Accordion.Path.Linear` | [`Path.lean:54`](Accordion/Path.lean#L54) |

#### 2B. WhileFS syntax

| Paper       | Section/Figure | Lean                  | File                                            |
| ----------- | -------------- | --------------------- | ----------------------------------------------- |
| FileType y  | Fig. 2         | `Accordion.FileType`  | [`WhileFS.lean:9`](Accordion/WhileFS.lean#L9) |
| Directory Δ | Fig. 4         | `Accordion.Directory` | [`WhileFS.lean:23`](Accordion/WhileFS.lean#L23) |
| Val v       | Fig. 2, Fig. 4 | `Accordion.Val`       | [`WhileFS.lean:26`](Accordion/WhileFS.lean#L26) |
| Expr e      | Fig. 2         | `Accordion.Expr`      | [`WhileFS.lean:34`](Accordion/WhileFS.lean#L34) |
| Command c   | Fig. 2         | `Accordion.Command`   | [`WhileFS.lean:47`](Accordion/WhileFS.lean#L47) |
| Store ρ     | Fig. 4         | `Accordion.Store`     | [`WhileFS.lean:64`](Accordion/WhileFS.lean#L64) |
| State ς     | Fig. 4         | `Accordion.State`     | [`WhileFS.lean:78`](Accordion/WhileFS.lean#L78) |

#### 2C. File trees, one-holed contexts, path resolution

| Paper         | Section/Figure | Lean                                 | File                                                              |
| ------------- | -------------- | ------------------------------------ | ----------------------------------------------------------------- |
| FileTree τ    | Fig. 3         | `Accordion.FileTree`                 | [`FileTree.lean:11`](Accordion/FileTree.lean#L11)                 |
| FileEntries δ | Fig. 3         | `Accordion.FileTree.Entries`         | [`FileTree/Entries.lean:9`](Accordion/FileTree/Entries.lean#L9) |
| FTFocus f     | Fig. 3         | `Accordion.FileTree.Focus`           | [`FileTree.lean:25`](Accordion/FileTree.lean#L25)                 |
| FTCtx C       | Fig. 3         | `Accordion.FileTree.Ctx`             | [`FileTree.lean:34`](Accordion/FileTree.lean#L34)                 |
| C[f]          | Fig. 3         | `Accordion.FileTree.Ctx.fill`        | [`FileTree.lean:50`](Accordion/FileTree.lean#L50)                 |
| path C        | Fig. 4         | `Accordion.FileTree.Ctx.path`        | [`FileTree.lean:63`](Accordion/FileTree.lean#L63)                 |
| zipper z      | §3.3           | `Accordion.FileTree.Zipper`          | [`FileTree/Zipper.lean:15`](Accordion/FileTree/Zipper.lean#L15)   |
| traverse p z  | Fig. 3         | `Accordion.FileTree.Zipper.traverse` | [`FileTree/Zipper.lean:58`](Accordion/FileTree/Zipper.lean#L58)   |
| resolve p τ   | Fig. 3         | `Accordion.FileTree.resolve`         | [`FileTree/Zipper.lean:67`](Accordion/FileTree/Zipper.lean#L67)   |

#### 2D. Concrete operational semantics of WhileFS

| Paper                         | Section/Figure | Lean                  | File                                              |
| ----------------------------- | -------------- | --------------------- | ------------------------------------------------- |
| e ⇓<sup>ρ</sup> v             | Fig. 4         | `Accordion.Eval`      | [`WhileFS.lean:83`](Accordion/WhileFS.lean#L83)   |
| (c, ς) ⟶<sup>1</sup> (c′, ς′) | Fig. 4         | `Accordion.Step`      | [`WhileFS.lean:149`](Accordion/WhileFS.lean#L149) |
| (c, ς) ⟶<sup>\*</sup> (c′, ς′)           | §3.3           | `Accordion.Multistep` | [`WhileFS.lean:267`](Accordion/WhileFS.lean#L267) |

#### 2E. TWE

| Paper               | Section/Figure | Lean                                                                         | File                                                                                       |
| ------------------- | -------------- | ---------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------ |
| Name A              | Fig. 5         | `Accordion.TWE.Name`                                                         | [`TWE.lean:59`](Accordion/TWE.lean#L59)                                                    |
| Comp B              | Fig. 5         | `Accordion.TWE.Component`                                                    | [`TWE.lean:64`](Accordion/TWE.lean#L64)                                                    |
| Path P, Q           | Fig. 5         | `Accordion.TWE.Path`                                                         | [`TWE.lean:72`](Accordion/TWE.lean#L72)                                                    |
| Tree T              | Fig. 5         | `Accordion.TWE.Tree`                                                         | [`TWE.lean:81`](Accordion/TWE.lean#L81)                                                    |
| Names S             | Fig. 5         | `Accordion.TWE.Set`                                                          | [`TWE.lean:114`](Accordion/TWE.lean#L114)                                                  |
| Shape H             | Fig. 5         | `Accordion.TWE.Shape`                                                        | [`TWE.lean:12`](Accordion/TWE.lean#L12)                                                    |
| Prop Φ              | Fig. 5         | `Accordion.TWE.Atom`, `Accordion.Formula`                                    | [`TWE.lean:156`](Accordion/TWE.lean#L156), [`Formula.lean:10`](Accordion/Formula.lean#L10) |
| model ⟨σ, θ⟩        | Fig. 5         | `Accordion.TWE.Model`                                                        | [`TWE.lean:178`](Accordion/TWE.lean#L178)                                                  |
| ⟦P⟧<sub>σ,θ</sub>   | Fig. 5         | `Accordion.TWE.Model.evalPath`                                               | [`TWE.lean:232`](Accordion/TWE.lean#L232)                                                  |
| ⟦T⟧<sub>σ,θ</sub>   | Fig. 5         | `Accordion.TWE.Model.evalTree`                                               | [`TWE.lean:241`](Accordion/TWE.lean#L241)                                                  |
| ⟦S⟧<sub>σ,θ</sub>   | Fig. 5         | `Accordion.TWE.Model.evalNameSet`                                            | [`TWE.lean:256`](Accordion/TWE.lean#L256)                                                  |
| shape f             | Fig. 5         | `Accordion.FileTree.Focus.shape`                                             | [`TWE.lean:23`](Accordion/TWE.lean#L23)                                                    |
| ⟨σ, θ⟩ ⊨ Φ          | Fig. 5         | `Accordion.TWE.Model.satAtom`, `Accordion.Formula.sat`                       | [`TWE.lean:268`](Accordion/TWE.lean#L268), [`Formula.lean:51`](Accordion/Formula.lean#L51) |
| SAT(Φ)              | §4.2           | `Accordion.TWE.Formula.SAT`, over models satisfying `Accordion.TWE.Model.WF` | [`TWE.lean:305`](Accordion/TWE.lean#L305), [`TWE.lean:297`](Accordion/TWE.lean#L297)       |

#### 2F. Symbolic operational semantics of WhileFS

| Paper                                 | Section/Figure | Lean                           | File                                                                |
| ------------------------------------- | -------------- | ------------------------------ | ------------------------------------------------------------------- |
| symbolic values                       | Fig. 6         | `Accordion.SVal`               | [`WhileFS/Symbolic.lean:14`](Accordion/WhileFS/Symbolic.lean#L14)   |
| symbolic store ρ̂                      | Fig. 6         | `Accordion.SStore`             | [`WhileFS/Symbolic.lean:83`](Accordion/WhileFS/Symbolic.lean#L83)   |
| symbolic state ⟨ρ̂, T, π̂⟩              | Fig. 6         | `Accordion.SState`             | [`WhileFS/Symbolic.lean:91`](Accordion/WhileFS/Symbolic.lean#L91)   |
| ⟦⟨ρ̂, T, π̂⟩⟧<sub>σ,θ</sub>             | §4.2           | `Accordion.SState.instantiate` | [`WhileFS/Symbolic.lean:100`](Accordion/WhileFS/Symbolic.lean#L100) |
| e evaluates to v̂ under ρ̂, generating Φ | Fig. 6    | `Accordion.SEval`              | [`WhileFS/Symbolic.lean:111`](Accordion/WhileFS/Symbolic.lean#L111) |
| (c, ς̂) ⟶<sup>1</sup> (c′, ς̂′)         | Fig. 6         | `Accordion.SStep`              | [`WhileFS/Symbolic.lean:175`](Accordion/WhileFS/Symbolic.lean#L175) |
| (c, ς̂) ⟶<sup>\*</sup> (c′, ς̂′)                   | §4.2           | `Accordion.SMultistep`         | [`WhileFS/Symbolic.lean:312`](Accordion/WhileFS/Symbolic.lean#L312) |

#### 2G. Theorem 1, soundness

Soundness in Theorem 1 (§4.2) is proved by [`Accordion.WhileFS.Symbolic.soundness`](Accordion/WhileFS/Symbolic/Adequacy.lean#L14).

**Paper** (§4.2):

> **Soundness.**
> If (c, ⟨ρ̂, T, π̂⟩) ⟶<sup>\*</sup> (c′, ⟨ρ̂′, T′, π̂′⟩), then for every ⟨σ, θ⟩ ⊨ π̂′, it is the case that (c, ⟦⟨ρ̂, T, π̂⟩⟧<sub>σ,θ</sub>) ⟶<sup>\*</sup> (c′, ⟦⟨ρ̂′, T′, π̂′⟩⟧<sub>σ,θ</sub>).

**Lean** ([`WhileFS/Symbolic/Adequacy.lean:14`](Accordion/WhileFS/Symbolic/Adequacy.lean#L14)):

```lean
variable {Γ X : Type} {V : TWE.Vars} [Ord Γ] [DecidableEq Γ] [DecidableEq X]
  [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
  {c c' : Command Γ X} {ς ς' : State Γ X} {sς sς' : SState Γ X V}
  {m : TWE.Model Γ V}

theorem soundness :
    ((c, sς) ⇝* (c', sς')) → m.WF → (m ⊫ sς) → (m ⊨ sς'.π) →
      ⟦sς⟧  m = some ς  →
      ⟦sς'⟧ m = some ς' →
      ((c, ς) ⟶* (c', ς'))
```

Beyond the paper's statement, the Lean statement assumes that `m` is well-formed (`m.WF`), that `m` also satisfies the initial state (`m ⊫ sς`), and that both instantiations are defined (`= some ς`, `= some ς'`).

#### 2H. Theorem 1, completeness

Completeness in Theorem 1 (§4.2) is proved by [`Accordion.WhileFS.Symbolic.completeness`](Accordion/WhileFS/Symbolic/Adequacy.lean#L22).

**Paper** (§4.2):

> **Completeness.**
> If ⟨σ, θ⟩ ⊨ π̂, and ς = ⟦⟨ρ̂, T, π̂⟩⟧<sub>σ,θ</sub>, and (c, ς) ⟶<sup>\*</sup> (c′, ς′), then (c, ⟨ρ̂, T, π̂⟩) ⟶<sup>\*</sup> (c′, ⟨ρ̂′, T′, π̂′⟩), and there exists ⟨σ′, θ′⟩ such that ⟨σ′, θ′⟩ ⊨ π̂′, and ς = ⟦⟨ρ̂, T, π̂⟩⟧<sub>σ′,θ′</sub>, and ς′ = ⟦⟨ρ̂′, T′, π̂′⟩⟧<sub>σ′,θ′</sub>.

**Lean** ([`WhileFS/Symbolic/Adequacy.lean:22`](Accordion/WhileFS/Symbolic/Adequacy.lean#L22)):

```lean
variable {Γ X : Type} {V : TWE.Vars} [Ord Γ] [DecidableEq Γ] [DecidableEq X]
  [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
  {c c' : Command Γ X} {ς ς' : State Γ X} {sς sς' : SState Γ X V}
  {m : TWE.Model Γ V}

theorem completeness [TWE.Vars.Comparable V] [TWE.Vars.Unbounded V] :
    m.WF → (m ⊫ sς) → ⟦sς⟧ m = some ς → ((c, ς) ⟶* (c', ς')) →
      ∃ sς', ((c, sς) ⇝* (c', sς')) ∧
        ∃ m' : TWE.Model Γ V, m'.WF ∧ (m' ⊫ sς') ∧
          ⟦sς⟧  m' = some ς  ∧
          ⟦sς'⟧ m' = some ς'
```

Beyond the paper's statement, the Lean statement assumes that `m` is well-formed (`m.WF`) and that every value in the initial store instantiates under `m` (the second part of `m ⊫ sς`).
Its conclusion also gives that `m'` is well-formed and that every value in the final store instantiates under `m'`.

### Step 3: Hardness of TWE

#### 3A. WE Logics

| Paper            | Section/Figure | Lean                    | File                                             |
| ---------------- | -------------- | ----------------------- | ------------------------------------------------ |
| WE               | §5             | `Accordion.WE.Formula`          | [`WE.lean:48`](Accordion/WE.lean#L48)                   |
| WE + LEN         | §5             | `Accordion.WE.Len.Formula`      | [`WE/Len.lean:29`](Accordion/WE/Len.lean#L29)           |
| WE + NORM        | §5.1           | `Accordion.WE.Norm.Formula`     | [`WE/Norm.lean:30`](Accordion/WE/Norm.lean#L30)         |
| WE + WALK        | §5.1           | `Accordion.WE.Walk.Formula`     | [`WE/Walk.lean:34`](Accordion/WE/Walk.lean#L34)         |
| WE + SHAPE + REG | §5.2           | `Accordion.WE.ShapeReg.Formula` | [`WE/ShapeReg.lean:57`](Accordion/WE/ShapeReg.lean#L57) |

In each file, the atoms and the model of the logic are defined just before and after its `Formula`.

#### 3B. Hardness Reductions

| Paper                     | Section/Figure | Lean                                  | File                                                                |
| ------------------------- | -------------- | ------------------------------------- | ------------------------------------------------------------------- |
| ⦇·⦈ into WE + NORM        | §5.1           | `Accordion.WE.Len.Formula.toNorm`     | [`WE/Len/ToNorm.lean:18`](Accordion/WE/Len/ToNorm.lean#L18)         |
| ⦇·⦈ into WE + WALK        | §5.1           | `Accordion.WE.Len.Formula.toWalk`     | [`WE/Len/ToWalk.lean:18`](Accordion/WE/Len/ToWalk.lean#L18)         |
| reduction into WE + SHAPE + REG | §5.2           | `Accordion.WE.Len.Formula.toShapeReg` | [`WE/Len/ToShapeReg.lean:18`](Accordion/WE/Len/ToShapeReg.lean#L18) |
| ⦇·⦈ into TWE              | §5             | `Accordion.WE.Len.Formula.toTWE`      | [`WE/Len/ToTWE.lean:20`](Accordion/WE/Len/ToTWE.lean#L20)           |

The Lean statements of steps 3C to 3H are all in [`TWE/Hardness.lean`](Accordion/TWE/Hardness.lean), namespace `Accordion.WE.Len`, where `Formula` is `Len.Formula`, `Γ : Type` and `V : WE.Vars` are implicit, and every statement takes `[Inhabited Γ]` from the `variable` line of the file.

#### 3C. Theorem 2

Theorem 2 (§5.1) is proved by [`Accordion.WE.Len.toNorm_equisat`](Accordion/TWE/Hardness.lean#L18).

**Paper** (§5.1):

> **Theorem 2 (WE + LEN reduces to WE + NORM).**
> There exists ⦇·⦈ such that for any WE + LEN formula Φ, SAT<sub>WE + LEN</sub>(Φ) if and only if SAT<sub>WE + NORM</sub>(⦇Φ⦈).

**Lean** ([`TWE/Hardness.lean:18`](Accordion/TWE/Hardness.lean#L18)):

```lean
theorem toNorm_equisat (φ : Formula Γ V) :
    Norm.Formula.SAT (Formula.toNorm φ) ↔ Formula.SAT φ
```

#### 3D. Theorem 3

Theorem 3 (§5.1) is proved by [`Accordion.WE.Len.toWalk_equisat`](Accordion/TWE/Hardness.lean#L23).

**Paper** (§5.1):

> **Theorem 3 (WE + LEN reduces to WE + WALK).**
> There exists ⦇·⦈ such that for any WE + LEN formula Φ, SAT<sub>WE + LEN</sub>(Φ) if and only if SAT<sub>WE + WALK</sub>(⦇Φ⦈).

**Lean** ([`TWE/Hardness.lean:23`](Accordion/TWE/Hardness.lean#L23)):

```lean
theorem toWalk_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    (φ : Formula Γ V) :
    Walk.Formula.SAT (Formula.toWalk φ) ↔ Formula.SAT φ
```

#### 3E. WE + LEN reduces to WE + SHAPE + REG

The reduction of WE + LEN to WE + SHAPE + REG (§5.2) is proved by [`Accordion.WE.Len.toShapeReg_equisat`](Accordion/TWE/Hardness.lean#L29).

**Paper** (§5.2, which states the result in prose and has no theorem):

> Interestingly, length equalities can be recovered if regular constraints on paths are added to this fragment.

**Lean** ([`TWE/Hardness.lean:29`](Accordion/TWE/Hardness.lean#L29)):

```lean
theorem toShapeReg_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    (φ : Formula Γ V) :
    ShapeReg.Formula.SAT (Formula.toShapeReg φ) ↔ Formula.SAT φ
```

#### 3F. WE + LEN reduces to TWE

The reduction of WE + LEN to TWE (§5) is proved by [`Accordion.WE.Len.toTWE_equisat`](Accordion/TWE/Hardness.lean#L35).

**Paper** (§5):

> [TWE] encodes the theory of word equations with length constraints (WE + LEN).

**Lean** ([`TWE/Hardness.lean:35`](Accordion/TWE/Hardness.lean#L35)):

```lean
theorem toTWE_equisat [Ord Γ] [DecidableEq Γ] (φ : Formula Γ V) :
    TWE.Formula.SAT (Formula.toTWE φ) ↔ Formula.SAT φ
```

#### 3G. WE + LEN reduces to TWE, through WE + NORM

The reduction of WE + LEN to TWE through WE + NORM (§5) is proved by [`Accordion.WE.Len.toTWE_toNorm_equisat`](Accordion/TWE/Hardness.lean#L40).

**Lean** ([`TWE/Hardness.lean:40`](Accordion/TWE/Hardness.lean#L40)):

```lean
theorem toTWE_toNorm_equisat [Ord Γ] [DecidableEq Γ] (φ : Formula Γ V) :
    TWE.Formula.SAT (Norm.Formula.toTWE (Formula.toNorm φ)) ↔ Formula.SAT φ
```

#### 3H. WE + LEN reduces to TWE, through WE + WALK

The reduction of WE + LEN to TWE through WE + WALK (§5) is proved by [`Accordion.WE.Len.toTWE_toWalk_equisat`](Accordion/TWE/Hardness.lean#L45).

**Lean** ([`TWE/Hardness.lean:45`](Accordion/TWE/Hardness.lean#L45)):

```lean
theorem toTWE_toWalk_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    (φ : Formula Γ V) :
    TWE.Formula.SAT (Walk.Formula.toTWE (Formula.toWalk φ)) ↔ Formula.SAT φ
```

### Step 4: Decidability of linear TWE

#### 4A. Linear TWE

| Paper                         | Section/Figure | Lean                                | File                                                              |
| ----------------------------- | -------------- | ----------------------------------- | ----------------------------------------------------------------- |
| models of TWE<sub>↓</sub>     | §6.1           | `Accordion.TWE.Linear.Model`        | [`TWE/Linear.lean:43`](Accordion/TWE/Linear.lean#L43)             |
| SAT(Φ) for TWE<sub>↓</sub>    | §6.1           | `Accordion.TWE.Linear.Formula.SAT`  | [`TWE/Linear.lean:50`](Accordion/TWE/Linear.lean#L50)             |
| reduction of linear TWE to WE | §6.1           | `Accordion.TWE.Linear.Formula.toWE` | [`TWE/Linear/ToWE.lean:133`](Accordion/TWE/Linear/ToWE.lean#L133) |

#### 4B. Theorem 4

Equisatisfiability of the reduction of linear TWE to WE in Theorem 4 (§6.1) is proved by [`Accordion.TWE.Linear.toWE_equisat`](Accordion/TWE/Decidability.lean#L19).

**Paper** (§6.1):

> **Theorem 4.**
> There exists an equisatisfiable PSPACE reduction from TWE<sub>↓</sub> to WE.

**Lean** ([`TWE/Decidability.lean:19`](Accordion/TWE/Decidability.lean#L19)):

```lean
variable {Γ : Type} {V : Vars} [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
  [Vars.Comparable V] [Vars.Fresh V]

theorem toWE_equisat [Infinite Γ] (φ : TWE.Formula Γ V) :
    (∃ ψ ∈ Formula.toWE φ, WE.Formula.SAT ψ) ↔ Formula.SAT φ
```

The `variable` line of [`TWE/Decidability.lean`](Accordion/TWE/Decidability.lean#L14) gives the instance arguments shared by every statement of Steps 4 and 5.

As already noted, the PSPACE complexity of this reduction is not proved (see [Not claimed](#not-claimed)).

#### 4C. Decidability of WE and of linear TWE

The paper obtains decidability of linear TWE from Theorem 4 and the decidability of WE, the latter of which is proven by prior work.
The artifact proves both: [`Accordion.WE.Formula.sat?_iff`](Accordion/WE/Decidability.lean#L16) for WE and [`Accordion.TWE.Linear.sat?_iff`](Accordion/TWE/Decidability.lean#L28) for linear TWE.
Each is followed by the `DecidablePred` instance for satisfiability, which makes `SAT φ` usable in `if` and `decide`.

**Lean** ([`WE/Decidability.lean:12`](Accordion/WE/Decidability.lean#L12)):

```lean
variable {Γ : Type} {V : Vars} [DecidableEq Γ] [Fresh Γ] [DecidableEq V.Letter]
  [DecidableEq V.Word] [Fresh V.Word]

def Formula.sat? (φ : Formula Γ V) : Bool

theorem Formula.sat?_iff (φ : Formula Γ V) : φ.sat? = true ↔ φ.SAT

instance : DecidablePred (Formula.SAT (Γ := Γ) (V := V))
```

**Lean** ([`TWE/Decidability.lean:24`](Accordion/TWE/Decidability.lean#L24)):

```lean
def Formula.sat? [Fresh Γ] (φ : TWE.Formula Γ V) : Bool :=
  (Formula.toWE φ).any WE.Formula.sat?

theorem sat?_iff [Fresh Γ] (φ : TWE.Formula Γ V) : Formula.sat? φ = true ↔ Formula.SAT φ

instance [Fresh Γ] : DecidablePred (Formula.SAT (Γ := Γ) (V := V))
```

The complexity of the decision procedures is not proved (see [Not claimed](#not-claimed)).

### Step 5: Decidability of bounded TWE

#### 5A. Bounded TWE

| Paper                                             | Section/Figure | Lean                                     | File                                                                      |
| ------------------------------------------------- | -------------- | ---------------------------------------- | ------------------------------------------------------------------------- |
| models of TWE<sub>k</sub>                         | §6.2           | `Accordion.TWE.Bounded.Model`            | [`TWE/Bounded.lean:25`](Accordion/TWE/Bounded.lean#L25)                   |
| SAT(Φ) for TWE<sub>k</sub>                        | §6.2           | `Accordion.TWE.Bounded.Formula.SAT`      | [`TWE/Bounded.lean:32`](Accordion/TWE/Bounded.lean#L32)                   |
| reduction of bounded non-linear TWE to linear TWE | §6.2           | `Accordion.TWE.Bounded.Formula.toLinear` | [`TWE/Bounded/ToLinear.lean:19`](Accordion/TWE/Bounded/ToLinear.lean#L19) |
| reduction of bounded non-linear TWE to WE         | §6.2           | `Accordion.TWE.Bounded.Formula.toWE`     | [`TWE/Bounded/ToWE.lean:18`](Accordion/TWE/Bounded/ToWE.lean#L18)         |

#### 5B. Theorem 5, bounded TWE reduces to linear TWE

Equisatisfiability of the reduction to linear TWE in Theorem 5 (§6.2) is proved by [`Accordion.TWE.Bounded.toLinear_equisat`](Accordion/TWE/Decidability.lean#L41).

**Paper** (§6.2):

> **Theorem 5.**
> Given a TWE<sub>k</sub> formula Φ with bound k, there is an equisatisfiable reduction to TWE<sub>↓</sub>...

**Lean** ([`TWE/Decidability.lean:41`](Accordion/TWE/Decidability.lean#L41)):

```lean
theorem toLinear_equisat [Nonempty Γ] (k : Nat) (φ : TWE.Formula Γ V) :
    (∃ ψ ∈ Formula.toLinear k φ, Linear.Formula.SAT ψ) ↔ Formula.SAT k φ
```

As already noted, the space bound of this reduction is not proved (see [Not claimed](#not-claimed)).

#### 5C. Theorem 5, bounded TWE reduces to WE

Equisatisfiability of the reduction to WE in Theorem 5 (§6.2) is proved by [`Accordion.TWE.Bounded.toWE_equisat`](Accordion/TWE/Decidability.lean#L46).

**Paper** (§6.2):

> **Theorem 5.**
> Given a TWE<sub>k</sub> formula Φ with bound k, there is an equisatisfiable reduction... to WE...

**Lean** ([`TWE/Decidability.lean:46`](Accordion/TWE/Decidability.lean#L46)):

```lean
theorem toWE_equisat [Infinite Γ] (k : Nat) (φ : TWE.Formula Γ V) :
    (∃ ψ ∈ Formula.toWE k φ, WE.Formula.SAT ψ) ↔ Formula.SAT k φ
```

As already noted, the space bound of this reduction is not proved (see [Not claimed](#not-claimed)).

#### 5D. Decidability of bounded TWE

Decidability of bounded TWE follows from Theorem 5 and the decidability of WE (see [Step 4C](#4c-decidability-of-we-and-of-linear-twe)), and is proved by [`Accordion.TWE.Bounded.sat?_iff`](Accordion/TWE/Decidability.lean#L55), followed by the `DecidablePred` instance for satisfiability.

**Lean** ([`TWE/Decidability.lean:51`](Accordion/TWE/Decidability.lean#L51)):

```lean
def Formula.sat? [Fresh Γ] (k : Nat) (φ : TWE.Formula Γ V) : Bool :=
  (Formula.toWE k φ).any WE.Formula.sat?

theorem sat?_iff [Fresh Γ] (k : Nat) (φ : TWE.Formula Γ V) :
    Formula.sat? k φ = true ↔ Formula.SAT k φ

instance [Fresh Γ] (k : Nat) : DecidablePred (Formula.SAT (Γ := Γ) (V := V) k)
```

The complexity of the decision procedure is not proved (see [Not claimed](#not-claimed)).

## Milestone 3: Reusing the artifact (Reusable)

### Dependencies

-   Lean, v4.34.1
-   mathlib, v4.34.1

### File structure

- [`lakefile.toml`](lakefile.toml): project configuration
- [`lake-manifest.json`](lake-manifest.json): exact revisions of dependencies
- [`lean-toolchain`](lean-toolchain): toolchain version
- [`Axioms.lean`](Axioms.lean): `#print axioms` for theorems
- [`Accordion.lean`](Accordion.lean): imports every specification file
- `Accordion/`
  - [`Path.lean`](Accordion/Path.lean): paths and components
  - `Path/`
    - [`Properties.lean`](Accordion/Path/Properties.lean): helper lemmas
    - [`StrictPrefix.lean`](Accordion/Path/StrictPrefix.lean): strict prefixes of paths
    - [`Measures.lean`](Accordion/Path/Measures.lean): lemmas about anchored and balanced paths
    - `Measures/`
      - [`Defs.lean`](Accordion/Path/Measures/Defs.lean): anchored and balanced paths
      - [`Properties.lean`](Accordion/Path/Measures/Properties.lean): helper lemmas
  - [`FileTree.lean`](Accordion/FileTree.lean): file trees, one-holed contexts
  - `FileTree/`
    - [`Properties.lean`](Accordion/FileTree/Properties.lean): helper lemmas
    - [`Entries.lean`](Accordion/FileTree/Entries.lean): directory entries
    - `Entries/`
      - [`Properties.lean`](Accordion/FileTree/Entries/Properties.lean): helper lemmas
    - [`Zipper.lean`](Accordion/FileTree/Zipper.lean): path resolution
    - `Zipper/`
      - [`Properties.lean`](Accordion/FileTree/Zipper/Properties.lean): helper lemmas
  - [`WhileFS.lean`](Accordion/WhileFS.lean): WhileFS syntax and concrete semantics
  - `WhileFS/`
    - [`Notation.lean`](Accordion/WhileFS/Notation.lean): notation for writing programs
    - [`Symbolic.lean`](Accordion/WhileFS/Symbolic.lean): symbolic semantics
    - `Symbolic/`
      - [`Soundness.lean`](Accordion/WhileFS/Symbolic/Soundness.lean): proof of soundness
      - [`Completeness.lean`](Accordion/WhileFS/Symbolic/Completeness.lean): proof of completeness
      - [`Adequacy.lean`](Accordion/WhileFS/Symbolic/Adequacy.lean): Theorem 1
      - [`Executions.lean`](Accordion/WhileFS/Symbolic/Executions.lean): inversion of symbolic executions
      - `Executions/`
        - [`Defs.lean`](Accordion/WhileFS/Symbolic/Executions/Defs.lean): helper definitions
  - [`Guess.lean`](Accordion/Guess.lean): nondeterministic computations
  - `Guess/`
    - [`Properties.lean`](Accordion/Guess/Properties.lean): helper lemmas
  - [`Fresh.lean`](Accordion/Fresh.lean): supply of fresh elements
  - [`Formula.lean`](Accordion/Formula.lean): connectives and satisfaction, shared by every logic
  - `Formula/`
    - [`Properties.lean`](Accordion/Formula/Properties.lean): helper lemmas
  - [`TWE.lean`](Accordion/TWE.lean): TWE
  - `TWE/`
    - [`Properties.lean`](Accordion/TWE/Properties.lean): helper lemmas
    - [`OfType.lean`](Accordion/TWE/OfType.lean): variables of every sort drawn from one type
    - [`Fresh.lean`](Accordion/TWE/Fresh.lean): free and fresh variables
    - `Fresh/`
      - [`Properties.lean`](Accordion/TWE/Fresh/Properties.lean): helper lemmas
    - [`Hardness.lean`](Accordion/TWE/Hardness.lean): Theorems 2 and 3, and the other theorems of §5
    - [`Decidability.lean`](Accordion/TWE/Decidability.lean): Theorems 4 and 5, decidability of linear and bounded TWE
    - [`Linear.lean`](Accordion/TWE/Linear.lean): linear TWE
    - `Linear/`
      - [`Properties.lean`](Accordion/TWE/Linear/Properties.lean): helper lemmas
      - [`ToWE.lean`](Accordion/TWE/Linear/ToWE.lean): reduction of linear TWE to WE
      - `ToWE/`
        - [`Intermediate.lean`](Accordion/TWE/Linear/ToWE/Intermediate.lean): intermediate fragments
        - [`Defs.lean`](Accordion/TWE/Linear/ToWE/Defs.lean): helper definitions
        - [`Rewrites.lean`](Accordion/TWE/Linear/ToWE/Rewrites.lean): rewrite rules
        - `Properties/`: helper definitions and lemmas, one file for each rewrite rule
    - [`Bounded.lean`](Accordion/TWE/Bounded.lean): bounded TWE
    - `Bounded/`
      - [`Properties.lean`](Accordion/TWE/Bounded/Properties.lean): helper lemmas
      - [`ToLinear.lean`](Accordion/TWE/Bounded/ToLinear.lean): reduction of bounded TWE to linear TWE
      - `ToLinear/`
        - [`Intermediate.lean`](Accordion/TWE/Bounded/ToLinear/Intermediate.lean): path decompositions
        - [`Defs.lean`](Accordion/TWE/Bounded/ToLinear/Defs.lean): helper definitions
        - [`Rewrites.lean`](Accordion/TWE/Bounded/ToLinear/Rewrites.lean): rewrite rules
        - `Properties/`: helper definitions and lemmas
      - [`ToWE.lean`](Accordion/TWE/Bounded/ToWE.lean): reduction of bounded TWE to WE
  - [`WE.lean`](Accordion/WE.lean): WE
  - `WE/`
    - [`Properties.lean`](Accordion/WE/Properties.lean): helper lemmas
    - [`Len.lean`](Accordion/WE/Len.lean): WE + LEN
    - `Len/`
      - [`ToNorm.lean`](Accordion/WE/Len/ToNorm.lean): reduction of WE + LEN to WE + NORM
      - [`ToWalk.lean`](Accordion/WE/Len/ToWalk.lean): reduction of WE + LEN to WE + WALK
      - [`ToShapeReg.lean`](Accordion/WE/Len/ToShapeReg.lean): reduction of WE + LEN to WE + SHAPE + REG
      - [`ToTWE.lean`](Accordion/WE/Len/ToTWE.lean): reductions of WE + LEN to TWE
      - [`ToLenEq.lean`](Accordion/WE/Len/ToLenEq.lean), `ToLenEq/`: helper reduction
    - [`LenEq.lean`](Accordion/WE/LenEq.lean), `LenEq/`: helper logic and its reductions
    - [`Norm.lean`](Accordion/WE/Norm.lean): WE + NORM
    - `Norm/`
      - [`ToTWE.lean`](Accordion/WE/Norm/ToTWE.lean), `ToTWE/`: embedding of WE + NORM into TWE
    - [`Walk.lean`](Accordion/WE/Walk.lean): WE + WALK
    - `Walk/`
      - [`ToTWE.lean`](Accordion/WE/Walk/ToTWE.lean), `ToTWE/`: embedding of WE + WALK into TWE
    - [`ShapeReg.lean`](Accordion/WE/ShapeReg.lean): WE + SHAPE + REG
    - [`Decidability.lean`](Accordion/WE/Decidability.lean): decidability of WE
    - `Decidability/`
      - [`Defs.lean`](Accordion/WE/Decidability/Defs.lean): helper definitions
      - [`Steps.lean`](Accordion/WE/Decidability/Steps.lean): steps of the decision procedure
      - `Properties/`: helper definitions and lemmas

### Using the library from another project

Add the artifact as a dependency in the other project's `lakefile.toml`:

```toml
[[require]]
name = "Accordion"
git = "https://github.com/atlas-brown/twe-artifact"
```

The project must use the toolchain in [`lean-toolchain`](lean-toolchain).
Run `lake update` and then `lake exe cache get`, so that mathlib is downloaded and not compiled.

`import Accordion` then gives every definition and theorem of the claims tables.

#### Example

The example below uses the library to prove that the program `create build/../build.log; mkdir build` can never execute to completion.
By completeness (theorem 1), a completed execution would give a symbolic execution whose path condition `π` is satisfiable; but `π` is not: it requires `build` to be both a directory and absent.

```lean
import Accordion

open Accordion WhileFS WhileFS.Symbolic
open scoped TWE Accordion.Formula

def build : Path String := ["build"]
abbrev log : Path String := build/‥ / "build.log"

abbrev program : Command String String := .create log ;; .mkdir build

-- The path condition of `program` in an unknown tree `T`.
abbrev V := TWE.Vars.ofType Nat
abbrev T : TWE.Tree V := .var (0 : Nat)
abbrev π (l l' : Nat) : TWE.Formula String V :=
  ⊤ ⋏ ⊤ ⋏ T ⊢ ⌜log⌝ ⇝ l ∶ .absent ⋏ ⊤ ⋏ T[l ↦ .file] ⊢ ⌜build⌝ ⇝ l' ∶ .absent

theorem π_unsat {m : TWE.Model String V} {l l'} (hm : m.WF) : ¬ m ⊨ π l l' := by grind

theorem program_never_completes {τ : FileTree String} {ς'} (hτ : τ.Canonical) :
    ¬ (program, ⟨∅, τ⟩) ⟶* (.skip, ς') := by
  intro hrun
  grind [completeness_init (V := V) (0 : Nat) hτ hrun, π_unsat]

#print axioms program_never_completes
```

To check this example without creating another project, save it as `Example.lean` in the root directory of the artifact and run:

```sh
lake env lean Example.lean
```

Lean checks the proofs in a few seconds and prints the axioms that the theorem depends on:

```
'program_never_completes' depends on axioms: [propext, Classical.choice, Quot.sound]
```
