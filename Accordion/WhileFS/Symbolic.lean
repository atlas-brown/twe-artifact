module

public import Accordion.WhileFS
public import Accordion.TWE.Properties
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finmap

@[expose] public section

namespace Accordion

open scoped TWE Accordion.Formula

/-- A symbolic value (Fig. 6). -/
inductive SVal (Γ : Type) (V : TWE.Vars) where
  | prop (Φ : TWE.Formula Γ V)
  | path (P : TWE.Path Γ V)
  | tree (T : TWE.Tree V)
  | set (S : TWE.Set Γ V)

variable {Γ X : Type} {V : TWE.Vars}

instance : Coe (TWE.Formula Γ V) (SVal Γ V) := ⟨SVal.prop⟩
instance : Coe (TWE.Path Γ V) (SVal Γ V) := ⟨SVal.path⟩
instance : Coe (TWE.Tree V) (SVal Γ V) := ⟨SVal.tree⟩
instance : Coe (TWE.Set Γ V) (SVal Γ V) := ⟨SVal.set⟩

def embedComponent : Component Γ → TWE.Component Γ V
  | .name a => .name (.name a)
  | .empty => .empty
  | .self => .self
  | .parent => .parent

def embedPath : Path Γ → TWE.Path Γ V
  | .nil => .nil
  | .app p q => embedPath p ++ .init (embedComponent q)

-- `Finset.sort`'s order side conditions, from `Γ`'s `Std` laws rather than a `LinearOrder Γ`.
local instance [Ord Γ] [Std.TransOrd Γ] : IsTrans Γ (fun a b => compare a b ≠ Ordering.gt) :=
  ⟨fun _ _ _ h₁ h₂ => Std.TransCmp.le_trans h₁ h₂⟩

local instance [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] :
    Std.Antisymm (fun a b : Γ => compare a b ≠ Ordering.gt) where
  antisymm a b h₁ h₂ := by
    cases hab : compare a b with
    | lt => exact absurd (Std.OrientedCmp.gt_of_lt hab) h₂
    | eq => exact Std.LawfulEqCmp.eq_of_compare hab
    | gt => exact absurd hab h₁

local instance [Ord Γ] [Std.TransOrd Γ] : Std.Total (fun a b : Γ => compare a b ≠ Ordering.gt) where
  total a b :=
    if h : compare a b = .gt then Or.inr (by simp [Std.OrientedCmp.lt_of_gt h]) else Or.inl h

-- `TWE.Set.insert` is order-sensitive as syntax, so the term is built from the sorted list.
def embedNameSet [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] (Δ : Finset Γ) :
    TWE.Set Γ V :=
  (Δ.sort (fun a b => compare a b ≠ .gt)).foldr (fun a acc => .insert (.name a) acc) ∅

def embed [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] : Val Γ → SVal Γ V
  | .bool b => .prop (if b then ⊤ else ⊥)
  | .path p => .path (embedPath p)
  | .filetype .file => .tree .file
  | .filetype .dirc => .tree .emptyDirc
  | .directory Δ => .set (embedNameSet Δ)

notation:max "⌜" v "⌝" => embedComponent v
notation:max "⌜" v "⌝" => embedPath v
notation:max "⌜" v "⌝" => embedNameSet v
notation:max "⌜" v "⌝" => embed v

variable [Ord Γ] [DecidableEq Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]

def SVal.instantiate : SVal Γ V → TWE.Model Γ V → Option (Val Γ)
  | .prop Φ, m => some (.bool (decide (m ⊨ Φ)))
  | .path P, m => some (.path (m.evalPath P))
  | .tree T, m => do
      match (← m.evalTree T).shape with
      | .file => some (.filetype .file)
      | .dirc => some (.filetype .dirc)
      | .absent => none
  | .set S, m => (m.evalNameSet S).map .directory

/-- A symbolic store, mapping program variables to symbolic values (Fig. 6). -/
abbrev SStore (Γ X : Type) (V : TWE.Vars) := Finmap (fun _ : X => SVal Γ V)

def SStore.set [DecidableEq X] (ρ : SStore Γ X V) (x : X) (v : SVal Γ V) : SStore Γ X V :=
  ρ.insert x v

macro:max (name := sstoreSetNotation) ρ:term:max noWs "[" x:term " ↦ " v:term "]" : term => `(SStore.set $ρ $x $v)

/-- A symbolic state: a symbolic store, a tree term and a path condition (Fig. 6). -/
structure SState (Γ X : Type) (V : TWE.Vars) where
  store : SStore Γ X V
  tree : TWE.Tree V
  π : TWE.Formula Γ V

def SStore.instantiate [DecidableEq X] (ρ : SStore Γ X V) (m : TWE.Model Γ V) : Store Γ X :=
  fun x => (ρ.lookup x).bind (·.instantiate m)

/-- The concrete state a symbolic state denotes in a model, if any (§4.2). -/
def SState.instantiate [DecidableEq X] (ς : SState Γ X V) (m : TWE.Model Γ V) : Option (State Γ X) :=
  match m.evalTree ς.tree with
  | some (.tree τ) => some ⟨ς.store.instantiate m, τ⟩
  | _ => none

-- The high priority reclaims `⟦ ⟧` from mathlib's `Quotient.mk` notation, so that `⟦v⟧ m` parses.
notation:max (priority := high) "⟦" v "⟧" => SVal.instantiate v
notation:max (priority := high) "⟦" ρ "⟧" => SStore.instantiate ρ
notation:max (priority := high) "⟦" ς "⟧" => SState.instantiate ς

/-- Symbolic evaluation `e ⇓[ρ] v ∣ Φ` (Fig. 6). -/
inductive SEval [DecidableEq X] (ρ : SStore Γ X V) : Expr Γ X → TWE.Formula Γ V → SVal Γ V → Prop
  | var {x v}
      : ρ.lookup x = some v
      → SEval ρ (.var x) ⊤ v
  | val {v}
      : SEval ρ (.val v) ⊤ (⌜v⌝)
  | pathEq {e₁ e₂ Φ₁ Φ₂ P₁ P₂}
      : SEval ρ e₁ Φ₁ (.path P₁)
      → SEval ρ e₂ Φ₂ (.path P₂)
      → SEval ρ (.eq e₁ e₂) (Φ₁ ⋏ Φ₂) (.prop (P₁ ≐ P₂))
  | boolEq {e₁ e₂ Φ₁ Φ₂ Φ₁' Φ₂'}
      : SEval ρ e₁ Φ₁ (.prop Φ₁')
      → SEval ρ e₂ Φ₂ (.prop Φ₂')
      → SEval ρ (.eq e₁ e₂) (Φ₁ ⋏ Φ₂) (.prop (Φ₁' ⇔ Φ₂'))
  | fileTypeEq {e₁ e₂ Φ₁ Φ₂ T₁ T₂}
      : SEval ρ e₁ Φ₁ (.tree T₁)
      → SEval ρ e₂ Φ₂ (.tree T₂)
      → SEval ρ (.eq e₁ e₂) (Φ₁ ⋏ Φ₂)
          (.prop (T₁ ∶ .file ⋏ T₂ ∶ .file ⋎ T₁ ∶ .dirc ⋏ T₂ ∶ .dirc
                    ⋎ T₁ ∶ .absent ⋏ T₂ ∶ .absent))
  | dirstreamEq {e₁ e₂ Φ₁ Φ₂ S₁ S₂}
      : SEval ρ e₁ Φ₁ (.set S₁)
      → SEval ρ e₂ Φ₂ (.set S₂)
      → SEval ρ (.eq e₁ e₂) (Φ₁ ⋏ Φ₂) (.prop (S₁ ≐ S₂))
  | not {e Φ Φ'}
      : SEval ρ e Φ (.prop Φ')
      → SEval ρ (.not e) Φ (.prop (∼Φ'))
  | and {e₁ e₂ Φ₁ Φ₂ Φ₁' Φ₂'}
      : SEval ρ e₁ Φ₁ (.prop Φ₁')
      → SEval ρ e₂ Φ₂ (.prop Φ₂')
      → SEval ρ (.and e₁ e₂) (Φ₁ ⋏ Φ₂) (.prop (Φ₁' ⋏ Φ₂'))
  | or {e₁ e₂ Φ₁ Φ₂ Φ₁' Φ₂'}
      : SEval ρ e₁ Φ₁ (.prop Φ₁')
      → SEval ρ e₂ Φ₂ (.prop Φ₂')
      → SEval ρ (.or e₁ e₂) (Φ₁ ⋏ Φ₂) (.prop (Φ₁' ⋎ Φ₂'))
  | join {e₁ e₂ Φ₁ Φ₂ P₁ P₂}
      : SEval ρ e₁ Φ₁ (.path P₁)
      → SEval ρ e₂ Φ₂ (.path P₂)
      → SEval ρ (.join e₁ e₂) (Φ₁ ⋏ Φ₂) (.path (P₁ ++ P₂))
  /-- Fresh `Z`, `YB`. -/
  | baseCons {e Φ P} (Z : V.Path) (YB : V.Comp)
      : SEval ρ e Φ (.path P)
      → SEval ρ (.base e)
          (Φ ⋏ P ≐ Z ++ YB)
          (.path YB)
  | baseEps {e Φ P}
      : SEval ρ e Φ (.path P)
      → SEval ρ (.base e) (Φ ⋏ P ≐ .nil) (.path .nil)
  /-- Fresh `Z`, `YB`. -/
  | dir {e Φ P} (Z : V.Path) (YB : V.Comp)
      : SEval ρ e Φ (.path P)
      → SEval ρ (.dir e)
          (Φ ⋏ (P ≐ Z ++ YB ⋎ P ≐ .nil ⋏ Z ≐ .nil))
          (.path Z)
  | norm {e Φ P}
      : SEval ρ e Φ (.path P)
      → SEval ρ (.norm e) Φ (.path (.norm P))

notation:50 e " ⇓[" ρ "] " v:51 " ∣ " Φ => SEval ρ e Φ v

section
variable [DecidableEq X]

/-- Symbolic small-step reduction `(c, sς) ⇝ (c', sς')` (Fig. 6). -/
inductive SStep : (c : Command Γ X) → (sς : SState Γ X V) → (c' : Command Γ X) →
    (sς' : SState Γ X V) → Prop
  | context {E : CmdCtx Γ X} {c sς c' sς'}
      : SStep c sς c' sς'
      → SStep (E.fill c)
          sς
          (E.fill c')
          sς'
  | assign {x e Φ v ρ T π π'}
      : (e ⇓[ρ] v ∣ Φ)
      → π' = π ⋏ Φ
      → TWE.Formula.SAT π'
      → SStep (.assign x e)
          ⟨ρ, T, π⟩
          .skip
          ⟨ρ[x ↦ v], T, π'⟩
  | seq {c sς}
      : SStep (.seq .skip c)
          sς
          c
          sς
  | ifTrue {e c₁ c₂ ρ T π Φ Φ' π'}
      : (e ⇓[ρ] (.prop Φ') ∣ Φ)
      → π' = π ⋏ Φ ⋏ Φ'
      → TWE.Formula.SAT π'
      → SStep (.cond e c₁ c₂)
          ⟨ρ, T, π⟩
          c₁
          ⟨ρ, T, π'⟩
  | ifFalse {e c₁ c₂ ρ T π Φ Φ' π'}
      : (e ⇓[ρ] (.prop Φ') ∣ Φ)
      → π' = π ⋏ Φ ⋏ ∼Φ'
      → TWE.Formula.SAT π'
      → SStep (.cond e c₁ c₂)
          ⟨ρ, T, π⟩
          c₂
          ⟨ρ, T, π'⟩
  | while {e c sς}
      : SStep (.while e c)
          sς
          (.cond e (.seq c (.while e c)) .skip)
          sς
  /-- Fresh location. -/
  | create {e P Φ ρ T π π'} (L : V.Loc)
      : (e ⇓[ρ] (.path P) ∣ Φ)
      → π' = π ⋏ Φ ⋏ T ⊢ P ⇝ L ∶ .absent
      → TWE.Formula.SAT π'
      → SStep (.create e)
          ⟨ρ, T, π⟩
          .skip
          ⟨ρ, T[L ↦ .file], π'⟩
  /-- Fresh location. -/
  | mkdir {e P Φ ρ T π π'} (L : V.Loc)
      : (e ⇓[ρ] (.path P) ∣ Φ)
      → π' = π ⋏ Φ ⋏ T ⊢ P ⇝ L ∶ .absent
      → TWE.Formula.SAT π'
      → SStep (.mkdir e)
          ⟨ρ, T, π⟩
          .skip
          ⟨ρ, T[L ↦ .emptyDirc], π'⟩
  /-- Fresh location. -/
  | unlink {e P Φ ρ T π π'} (L : V.Loc)
      : (e ⇓[ρ] (.path P) ∣ Φ)
      → π' = π ⋏ Φ ⋏ T ⊢ P ⇝ L ∶ .file
      → TWE.Formula.SAT π'
      → SStep (.unlink e)
          ⟨ρ, T, π⟩
          .skip
          ⟨ρ, T[L ↦ .abst], π'⟩
  /-- Fresh location. -/
  | rmdir {e P Φ ρ T π π'} (L : V.Loc)
      : (e ⇓[ρ] (.path P) ∣ Φ)
      → π' = π ⋏ Φ ⋏ (T ⊢ P ⇝ L ∶ .dirc ⋏ TWE.Set.entries T[L] ≐ ∅)
      → TWE.Formula.SAT π'
      → SStep (.rmdir e)
          ⟨ρ, T, π⟩
          .skip
          ⟨ρ, T[L ↦ .abst], π'⟩
  /-- Fresh locations. -/
  | rename {e₁ e₂ P₁ P₂ Φ₁ Φ₂ ρ T π π'} (L₁ L₂ : V.Loc)
      : (e₁ ⇓[ρ] (.path P₁) ∣ Φ₁)
      → (e₂ ⇓[ρ] (.path P₂) ∣ Φ₂)
      → π' = π ⋏ Φ₁ ⋏ Φ₂ ⋏
          (T ⊢ P₁ ⇝ L₁ ∶∼ .absent ⋏ T[L₁ ↦ .abst] ⊢ P₂ ⇝ L₂ ∶ .absent)
      → TWE.Formula.SAT π'
      → SStep (.rename e₁ e₂)
          ⟨ρ, T, π⟩
          .skip
          ⟨ρ, T[L₁ ↦ .abst][L₂ ↦ T[L₁]], π'⟩
  /-- Fresh location. -/
  | stat {x e P Φ ρ T π π'} (L : V.Loc)
      : (e ⇓[ρ] (.path P) ∣ Φ)
      → π' = π ⋏ Φ ⋏ T ⊢ P ⇝ L ∶∼ .absent
      → TWE.Formula.SAT π'
      → SStep (.stat x e)
          ⟨ρ, T, π⟩
          .skip
          ⟨ρ[x ↦ T[L]], T, π'⟩
  /-- Fresh location `L` and canonical output `Q`. -/
  | realpath {x e P Φ ρ T π π'} (L : V.Loc) (Q : V.Path)
      : (e ⇓[ρ] (.path P) ∣ Φ)
      → π' = π ⋏ Φ ⋏ (T ⊢ P ⇝ L ∶∼ .absent ⋏ Q ≐ L ⋏ Lin Q)
      → TWE.Formula.SAT π'
      → SStep (.realpath x e)
          ⟨ρ, T, π⟩
          .skip
          ⟨ρ[x ↦ Q], T, π'⟩
  /-- Fresh location `L` and directory contents `S`. -/
  | opendir {x e P Φ ρ T π π'} (L : V.Loc) (S : V.Set)
      : (e ⇓[ρ] (.path P) ∣ Φ)
      → π' = π ⋏ Φ ⋏ (T ⊢ P ⇝ L ∶ .dirc ⋏ S ≐ .entries T[L])
      → TWE.Formula.SAT π'
      → SStep (.opendir x e)
          ⟨ρ, T, π⟩
          .skip
          ⟨ρ[x ↦ S], T, π'⟩
  | readdirNil {r x y e S Φ ρ T π π'}
      : (e ⇓[ρ] (.set S) ∣ Φ)
      → π' = π ⋏ Φ ⋏ S ≐ ∅
      → TWE.Formula.SAT π'
      → SStep (.readdir r x y e)
          ⟨ρ, T, π⟩
          .skip
          ⟨(ρ[r ↦ (⊥ : TWE.Formula Γ V)])[x ↦ S], T, π'⟩
  /-- Fresh `R`, `XA`. -/
  | readdirCons {r x y e S Φ ρ T π π'} (R : V.Set) (XA : V.Name)
      : (e ⇓[ρ] (.set S) ∣ Φ)
      → π' = π ⋏ Φ ⋏ (S ≐ .insert XA R ⋏ ∼XA ∈̇ R)
      → TWE.Formula.SAT π'
      → SStep (.readdir r x y e)
          ⟨ρ, T, π⟩
          .skip
          ⟨((ρ[r ↦ (⊤ : TWE.Formula Γ V)])[x ↦ R])[y ↦ (XA : TWE.Path Γ V)], T, π'⟩

notation:50 "(" c ", " sς ")" " ⇝ " "(" c' ", " sς' ")" => SStep c sς c' sς'

/-- The reflexive-transitive closure of `SStep` (§4.2). -/
inductive SMultistep : (c : Command Γ X) → (sς : SState Γ X V) → (c' : Command Γ X) →
    (sς' : SState Γ X V) → Prop
  | refl {c sς}
      : SMultistep c sς c sς
  | single {c sς c' sς'}
      : SStep c sς c' sς'
      → SMultistep c sς c' sς'
  | trans {c sς c'' sς'' c' sς'}
      : SMultistep c sς c'' sς''
      → SStep c'' sς'' c' sς'
      → SMultistep c sς c' sς'

notation:50 "(" c ", " sς ")" " ⇝* " "(" c' ", " sς' ")" => SMultistep c sς c' sς'

end

/-- `ρ` is valid under `m`: every value stored in `ρ` instantiates under `m`. -/
def SStore.Valid [DecidableEq X] (ρ : SStore Γ X V) (m : TWE.Model Γ V) : Prop :=
  ∀ x v, ρ.lookup x = some v → (⟦v⟧ m).isSome

notation:50 m:51 " ⊩ " ρ:51 => SStore.Valid ρ m

/-- `m` satisfies `ς`: it lies on `ς`'s branch and every value in `ς`'s store
instantiates under it. -/
def SState.Sat [DecidableEq X] (ς : SState Γ X V) (m : TWE.Model Γ V) : Prop :=
  (m ⊨ ς.π) ∧ (m ⊩ ς.store)

notation:50 m:51 " ⊫ " ς:51 => SState.Sat ς m

@[app_unexpander SStore.set]
meta def unexpandSStoreSet : Lean.PrettyPrinter.Unexpander
  | `($_ $ρ $x $v) =>
      return Lean.mkNode ``sstoreSetNotation
        #[ρ, Lean.mkNode `group #[], Lean.mkAtom "[", x, Lean.mkAtom " ↦ ", v, Lean.mkAtom "]"]
  | _ => throw ()

end Accordion

end
