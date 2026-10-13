module

public import Accordion.TWE.Bounded.ToLinear.Defs

@[expose] public section

namespace Accordion

namespace TWE

namespace Bounded

namespace ToLinear

open scoped Accordion.Formula Linear.ToWE.BigConnectives

variable {Γ : Type} {V : TWE.Vars}

def stepEquation (C : Step) (Y : V.Loc) (Z : V.Path) (A : V.Name) : TWE.Formula Γ V :=
  match C with
  | .empty => Z ≐ Y
  | .self => Z ≐ Y
  | .parent => Y ≐ .nil ⋏ Z ≐ .nil ⋎ Y ≐ Z ++ A

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

/-- The normal prefixes of a decomposition, as fresh locations `Yᵢ` given by defining equations
over fresh paths `Zᵢ` and names `Aᵢ`. -/
def normalize (d : Decomposition Γ V) : FreshDefM Γ V (NormalPrefixes V) := do
  let Y ← freshLoc
  define (Y ≐ d.first)
  go Y d.rest
where
  go (Y : V.Loc) : List (Step × TWE.Path Γ V) → FreshDefM Γ V (NormalPrefixes V)
    | [] => return ⟨[], Y⟩
    | (C, B) :: rest => do
        let Z ← freshPath
        let A ← freshName
        let Y' ← freshLoc
        define (stepEquation C Y Z A)
        define (Y' ≐ Z ++ B)
        let result ← go Y' rest
        return ⟨Y :: result.prefixes, result.last⟩

/-- The decomposition `B₁ C₁ B₂ ⋯ Cₘ Bₘ₊₁` of a path, under the decomposition `δ` of the
variables. -/
def decomposePath (δ : VariableDecomposition V) :
    TWE.Path Γ V → FreshDefM Γ V (Decomposition Γ V)
  | .nil => return .nil
  | .init (.name a) => return .linear a
  | .init .empty => return .step .empty
  | .init .self => return .step .self
  | .init .parent => return .step .parent
  | .init (.var x) => return match δ.component x with
      | .name => .linear x
      | .empty => .step .empty
      | .self => .step .self
      | .parent => .step .parent
  | .join P Q => do return (← decomposePath δ P).append (← decomposePath δ Q)
  | .loc ℓ => return .linear ℓ
  | .var X => return .var (δ.path X)
  | .norm P => do return .linear (← normalize (← decomposePath δ P)).last

/-- The negated atoms are not in the paper. -/
def translate (δ : VariableDecomposition V) :
    Bool → TWE.Formula Γ V → FreshDefM Γ V (TWE.Formula Γ V)
  | true, .top | false, .bot => return ⊤
  | false, .top | true, .bot => return ⊥
  | true, .conj φ ψ => do return (← translate δ true φ) ⋏ (← translate δ true ψ)
  | false, .conj φ ψ => do return (← translate δ false φ) ⋎ (← translate δ false ψ)
  | true, .disj φ ψ => do return (← translate δ true φ) ⋎ (← translate δ true ψ)
  | false, .disj φ ψ => do return (← translate δ false φ) ⋏ (← translate δ false ψ)
  | positive, .neg φ => translate δ (!positive) φ
  | true, .atom (.pathEq P Q) => do
      let d ← decomposePath δ P
      let d' ← decomposePath δ Q
      return if d.steps = d'.steps then ⋀ B ∈ d.blocks.zip d'.blocks, B.1 ≐ B.2 else ⊥
  | false, .atom (.pathEq P Q) => do
      let d ← decomposePath δ P
      let d' ← decomposePath δ Q
      return if d.steps = d'.steps then ⋁ B ∈ d.blocks.zip d'.blocks, ∼(B.1 ≐ B.2) else ⊤
  | true, .atom (.pathIsLin P) => do
      let d ← decomposePath δ P
      return if d.rest.isEmpty then ⊤ else ⊥
  | false, .atom (.pathIsLin P) => do
      let d ← decomposePath δ P
      return if d.rest.isEmpty then ⊥ else ⊤
  | true, .atom (.treeWalk P T ℓ) => do
      let Y ← normalize (← decomposePath δ P)
      return T ⊢ Y.last ⇝ ℓ ⋏ ⋀ Yᵢ ∈ Y.prefixes, T[Yᵢ] ∶ .dirc
  | false, .atom (.treeWalk P T ℓ) => do
      let Y ← normalize (← decomposePath δ P)
      return ∼(T ⊢ Y.last ⇝ ℓ) ⋎ ⋁ Yᵢ ∈ Y.prefixes, ∼(T[Yᵢ] ∶ .dirc)
  | true, .atom (.treeShape T h) => return T ∶ h
  | false, .atom (.treeShape T h) => return ∼(T ∶ h)
  | true, .atom (.setEq S S') => return S ≐ S'
  | false, .atom (.setEq S S') => return ∼(S ≐ S')
  | true, .atom (.setMem A S) => return A ∈̇ S
  | false, .atom (.setMem A S) => return ∼(A ∈̇ S)

/-- The translation of `φ` under `δ`, with the defining equations of its fresh variables conjoined
at the top, outside any negation. -/
def linearTranslation (δ : VariableDecomposition V) (φ : TWE.Formula Γ V) : TWE.Formula Γ V :=
  let translation := (translate δ true φ).start (φ.free ∪ δ.free)
  (⋀ D ∈ translation.2, D) ⋏ translation.1

/-- The decompositions of the variables of `φ` with at most `k` non-linear components in each path
variable, between blocks that are fresh, pairwise distinct path variables. -/
def variableDecompositions (k : Nat) (φ : TWE.Formula Γ V) : Guess (VariableDecomposition V) := do
  let components ← assignments φ.compVars (guess ComponentKind.all)
  let steps ← assignments φ.pathVars (stepPatterns k)
  pure ⟨components, ((freshDecompositions steps).run φ.free).1⟩

def VariableDecomposition.isBounded (k : Nat) (δ : VariableDecomposition V)
    (φ : TWE.Formula Γ V) : Bool :=
  φ.paths.all fun path =>
    ((decomposePath δ path).start (φ.free ∪ δ.free)).1.rest.length ≤ k

def boundedDecompositions (k : Nat) (φ : TWE.Formula Γ V) : Guess (VariableDecomposition V) := do
  let δ ← variableDecompositions k φ
  guard (δ.isBounded k φ)
  pure δ

end ToLinear

end Bounded

end TWE

end Accordion

end
