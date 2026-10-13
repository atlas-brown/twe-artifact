module

public import Accordion.FileTree.Zipper

@[expose] public section

namespace Accordion

/-- The type of a file system node (Fig. 2). -/
inductive FileType where
  | file
  | dirc
  deriving DecidableEq, Repr

namespace FileTree

def fileType {Γ : Type} : FileTree Γ → FileType
  | .file => .file
  | .dirc _ => .dirc

end FileTree

/-- A directory value: the set of its entry names (Fig. 4). -/
abbrev Directory (Γ : Type) := Finset Γ

/-- A value (Fig. 2, Fig. 4). -/
inductive Val (Γ : Type) where
  | bool (b : Bool)
  | path (p : Path Γ)
  | filetype (y : FileType)
  | directory (Δ : Directory Γ)
  deriving DecidableEq

/-- An expression (Fig. 2). -/
inductive Expr (Γ X : Type) where
  | var (x : X)
  | val (v : Val Γ)
  | eq (e₁ e₂ : Expr Γ X)
  | not (e : Expr Γ X)
  | and (e₁ e₂ : Expr Γ X)
  | or (e₁ e₂ : Expr Γ X)
  | join (e₁ e₂ : Expr Γ X)
  | base (e : Expr Γ X)
  | dir (e : Expr Γ X)
  | norm (e : Expr Γ X)

/-- A command (Fig. 2). -/
inductive Command (Γ X : Type) where
  | skip
  | assign (x : X) (e : Expr Γ X)
  | seq (c₁ c₂ : Command Γ X)
  | cond (e : Expr Γ X) (c₁ c₂ : Command Γ X)
  | while (e : Expr Γ X) (c : Command Γ X)
  | create (e : Expr Γ X)
  | mkdir (e : Expr Γ X)
  | unlink (e : Expr Γ X)
  | rmdir (e : Expr Γ X)
  | rename (e₁ e₂ : Expr Γ X)
  | stat (x : X) (e : Expr Γ X)
  | realpath (x : X) (e : Expr Γ X)
  | opendir (x : X) (e : Expr Γ X)
  | readdir (r x y : X) (e : Expr Γ X)

/-- A store, mapping program variables to values (Fig. 4). -/
abbrev Store (Γ X : Type) := X → Option (Val Γ)

inductive CmdCtx (Γ X : Type) where
  | hole
  | seq (E : CmdCtx Γ X) (c : Command Γ X)

variable {Γ X : Type} [Ord Γ] [DecidableEq Γ]

def Store.set [DecidableEq X] (ρ : Store Γ X) (x : X) (v : Val Γ) : Store Γ X :=
  fun y => if y = x then some v else ρ y

macro:max (name := storeSetNotation) ρ:term:max noWs "[" x:term " ↦ " v:term "]" : term => `(Store.set $ρ $x $v)

/-- A program state: a store and a file tree (Fig. 4). -/
structure State (Γ X : Type) where
  store : Store Γ X
  tree : FileTree Γ

/-- Big-step evaluation `e ⇓[ρ] v` (Fig. 4). -/
inductive Eval (ρ : Store Γ X) : Expr Γ X → Val Γ → Prop
  | var {x v}
      : ρ x = some v
      → Eval ρ (.var x) v
  | val {v}
      : Eval ρ (.val v) v
  | eqTrue {e₁ e₂ v₁ v₂}
      : Eval ρ e₁ v₁
      → Eval ρ e₂ v₂
      → v₁ = v₂
      → Eval ρ (.eq e₁ e₂) (.bool true)
  | eqFalseBool {e₁ e₂ b₁ b₂}
      : Eval ρ e₁ (.bool b₁)
      → Eval ρ e₂ (.bool b₂)
      → b₁ ≠ b₂
      → Eval ρ (.eq e₁ e₂) (.bool false)
  | eqFalsePath {e₁ e₂ p₁ p₂}
      : Eval ρ e₁ (.path p₁)
      → Eval ρ e₂ (.path p₂)
      → p₁ ≠ p₂
      → Eval ρ (.eq e₁ e₂) (.bool false)
  | eqFalseFileType {e₁ e₂ y₁ y₂}
      : Eval ρ e₁ (.filetype y₁)
      → Eval ρ e₂ (.filetype y₂)
      → y₁ ≠ y₂
      → Eval ρ (.eq e₁ e₂) (.bool false)
  | eqFalseDirectory {e₁ e₂ Δ₁ Δ₂}
      : Eval ρ e₁ (.directory Δ₁)
      → Eval ρ e₂ (.directory Δ₂)
      → Δ₁ ≠ Δ₂
      → Eval ρ (.eq e₁ e₂) (.bool false)
  | not {e b}
      : Eval ρ e (.bool b)
      → Eval ρ (.not e) (.bool (!b))
  | and {e₁ e₂ b₁ b₂}
      : Eval ρ e₁ (.bool b₁)
      → Eval ρ e₂ (.bool b₂)
      → Eval ρ (.and e₁ e₂) (.bool (b₁ && b₂))
  | or {e₁ e₂ b₁ b₂}
      : Eval ρ e₁ (.bool b₁)
      → Eval ρ e₂ (.bool b₂)
      → Eval ρ (.or e₁ e₂) (.bool (b₁ || b₂))
  | join {e₁ e₂ p₁ p₂}
      : Eval ρ e₁ (.path p₁)
      → Eval ρ e₂ (.path p₂)
      → Eval ρ (.join e₁ e₂) (.path (p₁ ++ p₂))
  | base {e p}
      : Eval ρ e (.path p)
      → Eval ρ (.base e) (.path p.base)
  | dir {e p}
      : Eval ρ e (.path p)
      → Eval ρ (.dir e) (.path p.dir)
  | norm {e p}
      : Eval ρ e (.path p)
      → Eval ρ (.norm e) (.path p.norm)

@[inherit_doc] notation:50 e " ⇓[" ρ "] " v => Eval ρ e v

def CmdCtx.fill : CmdCtx Γ X → Command Γ X → Command Γ X
  | .hole, c => c
  | .seq E c₂, c => .seq (E.fill c) c₂

section
variable [DecidableEq X]

/-- Small-step reduction `(c, ς) ⟶ (c', ς')` (Fig. 4). -/
inductive Step : (c : Command Γ X) → (ς : State Γ X) → (c' : Command Γ X) →
    (ς' : State Γ X) → Prop
  | context {E : CmdCtx Γ X} {c ς c' ς'}
      : Step c ς c' ς'
      → Step (E.fill c)
          ς
          (E.fill c')
          ς'
  | assign {x e v ρ τ}
      : (e ⇓[ρ] v)
      → Step (.assign x e)
          ⟨ρ, τ⟩
          .skip
          ⟨ρ[x ↦ v], τ⟩
  | seq {c ς}
      : Step (.seq .skip c)
          ς
          c
          ς
  | ifTrue {e c₁ c₂ ρ τ}
      : (e ⇓[ρ] .bool true)
      → Step (.cond e c₁ c₂)
          ⟨ρ, τ⟩
          c₁
          ⟨ρ, τ⟩
  | ifFalse {e c₁ c₂ ρ τ}
      : (e ⇓[ρ] .bool false)
      → Step (.cond e c₁ c₂)
          ⟨ρ, τ⟩
          c₂
          ⟨ρ, τ⟩
  | while {e c ς}
      : Step (.while e c)
          ς
          (.cond e (.seq c (.while e c)) .skip)
          ς
  | create {e p ρ τ C τ'}
      : (e ⇓[ρ] .path p)
      → FileTree.resolve p τ = some (C, .abst)
      → C.fill (.tree .file) = some τ'
      → Step (.create e)
          ⟨ρ, τ⟩
          .skip
          ⟨ρ, τ'⟩
  | mkdir {e p ρ τ C τ'}
      : (e ⇓[ρ] .path p)
      → FileTree.resolve p τ = some (C, .abst)
      → C.fill (.tree (.dirc ∅)) = some τ'
      → Step (.mkdir e)
          ⟨ρ, τ⟩
          .skip
          ⟨ρ, τ'⟩
  | unlink {e p ρ τ C τ'}
      : (e ⇓[ρ] .path p)
      → FileTree.resolve p τ = some (C, .tree .file)
      → C.fill .abst = some τ'
      → Step (.unlink e)
          ⟨ρ, τ⟩
          .skip
          ⟨ρ, τ'⟩
  | rmdir {e p ρ τ C τ'}
      : (e ⇓[ρ] .path p)
      → FileTree.resolve p τ = some (C, .tree (.dirc ⟨[]⟩))
      → C.fill .abst = some τ'
      → Step (.rmdir e)
          ⟨ρ, τ⟩
          .skip
          ⟨ρ, τ'⟩
  | rename {e₁ e₂ p₁ p₂ ρ τ C₁ τ₁ τmid C₂ τ'}
      : (e₁ ⇓[ρ] .path p₁)
      → FileTree.resolve p₁ τ = some (C₁, .tree τ₁)
      → C₁.fill .abst = some τmid
      → (e₂ ⇓[ρ] .path p₂)
      → FileTree.resolve p₂ τmid = some (C₂, .abst)
      → C₂.fill (.tree τ₁) = some τ'
      → Step (.rename e₁ e₂)
          ⟨ρ, τ⟩
          .skip
          ⟨ρ, τ'⟩
  | stat {x e p ρ τ C τ'}
      : (e ⇓[ρ] .path p)
      → FileTree.resolve p τ = some (C, .tree τ')
      → Step (.stat x e)
          ⟨ρ, τ⟩
          .skip
          ⟨ρ[x ↦ (.filetype τ'.fileType)], τ⟩
  | realpath {x e p ρ τ C τ'}
      : (e ⇓[ρ] .path p)
      → FileTree.resolve p τ = some (C, .tree τ')
      → Step (.realpath x e)
          ⟨ρ, τ⟩
          .skip
          ⟨ρ[x ↦ (.path C.path)], τ⟩
  | opendir {x e p ρ τ C δ}
      : (e ⇓[ρ] .path p)
      → FileTree.resolve p τ = some (C, .tree (.dirc δ))
      → Step (.opendir x e)
          ⟨ρ, τ⟩
          .skip
          ⟨ρ[x ↦ (.directory (FileTree.Entries.dom δ))], τ⟩
  | readdirNil {r x y e ρ τ}
      : (e ⇓[ρ] .directory ∅)
      → Step (.readdir r x y e)
          ⟨ρ, τ⟩
          .skip
          ⟨(ρ[r ↦ (.bool false)])[x ↦ (.directory ∅)], τ⟩
  | readdirCons {r x y e ρ τ a Δ}
      : (e ⇓[ρ] .directory Δ)
      → a ∈ Δ
      → Step (.readdir r x y e)
          ⟨ρ, τ⟩
          .skip
          ⟨((ρ[r ↦ (.bool true)])[x ↦ (.directory (Δ.erase a))])[y ↦
            (.path (Path.init (.name a)))], τ⟩

notation:50 "(" c ", " ς ")" " ⟶ " "(" c' ", " ς' ")" => Step c ς c' ς'

/-- The reflexive-transitive closure of `Step` (§3.3). -/
inductive Multistep : (c : Command Γ X) → (ς : State Γ X) → (c' : Command Γ X) →
    (ς' : State Γ X) → Prop
  | refl {c ς}
      : Multistep c ς c ς
  | single {c ς c' ς'}
      : Step c ς c' ς'
      → Multistep c ς c' ς'
  | trans {c ς c'' ς'' c' ς'}
      : Multistep c ς c'' ς''
      → Step c'' ς'' c' ς'
      → Multistep c ς c' ς'

notation:50 "(" c ", " ς ")" " ⟶* " "(" c' ", " ς' ")" => Multistep c ς c' ς'

end

@[app_unexpander Store.set]
meta def unexpandStoreSet : Lean.PrettyPrinter.Unexpander
  | `($_ $ρ $x $v) =>
      return Lean.mkNode ``storeSetNotation
        #[ρ, Lean.mkNode `group #[], Lean.mkAtom "[", x, Lean.mkAtom " ↦ ", v, Lean.mkAtom "]"]
  | _ => throw ()

end Accordion

end
