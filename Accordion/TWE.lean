module

public import Accordion.FileTree.Zipper
public import Accordion.Formula

@[expose] public section

namespace Accordion

namespace TWE

/-- The shape of a node: absent, a file, or a directory (Fig. 5). -/
inductive Shape where
  | absent
  | file
  | dirc
  deriving DecidableEq, Repr

end TWE

namespace FileTree.Focus

/-- The shape of a focus (Fig. 5). -/
def shape {Γ : Type} : Focus Γ → TWE.Shape
  | .abst => .absent
  | .tree .file => .file
  | .tree (.dirc _) => .dirc

end FileTree.Focus

namespace TWE

structure NameVars where
  Name : Type

structure CompVars extends NameVars where
  Comp : Type

structure PathVars extends CompVars where
  Path : Type
  Loc : Type

structure TreeVars where
  Tree : Type
  Loc : Type

structure SetVars extends NameVars, TreeVars where
  Set : Type

structure Vars extends PathVars, SetVars

instance : Coe CompVars NameVars := ⟨CompVars.toNameVars⟩
instance : Coe PathVars CompVars := ⟨PathVars.toCompVars⟩
instance : Coe SetVars NameVars := ⟨SetVars.toNameVars⟩
instance : Coe SetVars TreeVars := ⟨SetVars.toTreeVars⟩
instance : Coe Vars PathVars := ⟨Vars.toPathVars⟩
instance : Coe Vars SetVars := ⟨Vars.toSetVars⟩

/-- A name term (Fig. 5). -/
inductive Name (Γ : Type) (V : NameVars) where
  | name (a : Γ)
  | var (x : V.Name)

/-- A component term (Fig. 5). -/
inductive Component (Γ : Type) (V : CompVars) where
  | empty
  | self
  | parent
  | name (a : Name Γ V)
  | var (x : V.Comp)

/-- A path term (Fig. 5). -/
inductive Path (Γ : Type) (V : PathVars) where
  | nil
  | init (b : Component Γ V)
  | join (p q : Path Γ V)
  | loc (l : V.Loc)
  | var (x : V.Path)
  | norm (p : Path Γ V)

/-- A tree term (Fig. 5). -/
inductive Tree (V : TreeVars) where
  | var (x : V.Tree)
  | file
  | emptyDirc
  | abst
  | select (τ : Tree V) (l : V.Loc)
  | update (τ : Tree V) (l : V.Loc) (τ' : Tree V)

def Tree.decEq {V : TreeVars} [DecidableEq V.Tree] [DecidableEq V.Loc] :
    (T U : Tree V) → Decidable (T = U)
  | .var x, .var y => decidable_of_iff (x = y) (by simp)
  | .file, .file | .emptyDirc, .emptyDirc | .abst, .abst => isTrue rfl
  | .select T l, .select U k =>
      have := decEq T U
      decidable_of_iff (T = U ∧ l = k) (by simp)
  | .update T l T', .update U k U' =>
      have := decEq T U
      have := decEq T' U'
      decidable_of_iff (T = U ∧ l = k ∧ T' = U') (by simp)
  | .var _, .file | .var _, .emptyDirc | .var _, .abst | .var _, .select _ _ | .var _, .update _ _ _
  | .file, .var _ | .file, .emptyDirc | .file, .abst | .file, .select _ _ | .file, .update _ _ _
  | .emptyDirc, .var _ | .emptyDirc, .file | .emptyDirc, .abst | .emptyDirc, .select _ _
  | .emptyDirc, .update _ _ _
  | .abst, .var _ | .abst, .file | .abst, .emptyDirc | .abst, .select _ _ | .abst, .update _ _ _
  | .select _ _, .var _ | .select _ _, .file | .select _ _, .emptyDirc | .select _ _, .abst
  | .select _ _, .update _ _ _
  | .update _ _ _, .var _ | .update _ _ _, .file | .update _ _ _, .emptyDirc
  | .update _ _ _, .abst | .update _ _ _, .select _ _ => isFalse nofun

instance {V : TreeVars} [DecidableEq V.Tree] [DecidableEq V.Loc] : DecidableEq (Tree V) :=
  Tree.decEq

/-- A name-set term (Fig. 5). -/
inductive Set (Γ : Type) (V : SetVars) where
  | var (x : V.Set)
  | empty
  | insert (a : Name Γ V) (s : Set Γ V)
  | entries (τ : Tree V)

instance {Γ : Type} {V : NameVars} : Coe V.Name (Name Γ V) := ⟨Name.var⟩
instance {Γ : Type} {V : CompVars} : Coe V.Comp (Component Γ V) := ⟨Component.var⟩
instance {Γ : Type} {V : CompVars} : Coe (Name Γ V) (Component Γ V) := ⟨Component.name⟩
instance {Γ : Type} {V : PathVars} : Coe V.Path (Path Γ V) := ⟨Path.var⟩
instance {Γ : Type} {V : PathVars} : Coe V.Loc (Path Γ V) := ⟨Path.loc⟩
instance {Γ : Type} {V : PathVars} : Coe (Component Γ V) (Path Γ V) := ⟨Path.init⟩
instance {V : TreeVars} : Coe V.Tree (Tree V) := ⟨Tree.var⟩
instance {Γ : Type} {V : SetVars} : Coe V.Set (Set Γ V) := ⟨Set.var⟩

instance {Γ : Type} {V : PathVars} : Append (Path Γ V) := ⟨Path.join⟩
instance {Γ : Type} {V : SetVars} : EmptyCollection (Set Γ V) := ⟨Set.empty⟩

scoped syntax:max (name := selectNotation) term:max noWs "[" term "]" : term

macro_rules (kind := selectNotation)
  | `($τ[$l]) => `(Tree.select $τ $l)

scoped syntax:max (name := updateNotation) term:max noWs "[" term " ↦ " term "]" : term

macro_rules (kind := updateNotation)
  | `($τ[$l ↦ $τ']) => `(Tree.update $τ $l $τ')

@[scoped app_unexpander Tree.select]
meta def unexpandSelect : Lean.PrettyPrinter.Unexpander
  | `($_ $τ $l) =>
      return Lean.mkNode ``selectNotation #[τ, Lean.mkAtom "[", l, Lean.mkAtom "]"]
  | _ => throw ()

@[scoped app_unexpander Tree.update]
meta def unexpandUpdate : Lean.PrettyPrinter.Unexpander
  | `($_ $τ $l $τ') =>
      return Lean.mkNode ``updateNotation
        #[τ, Lean.mkAtom "[", l, Lean.mkAtom " ↦ ", τ', Lean.mkAtom "]"]
  | _ => throw ()

/-- An atomic proposition of TWE (Fig. 5). -/
inductive Atom (Γ : Type) (V : Vars) where
  | pathEq (p q : Path Γ V)
  | pathIsLin (p : Path Γ V)
  | treeWalk (p : Path Γ V) (τ : Tree V) (l : V.Loc)
  | treeShape (τ : Tree V) (h : Shape)
  | setEq (s s' : Set Γ V)
  | setMem (a : Name Γ V) (s : Set Γ V)

/-- A TWE formula (Fig. 5). -/
abbrev Formula (Γ : Type) (V : Vars) := Accordion.Formula (Atom Γ V)

open scoped Accordion.Formula

-- Atoms above the connectives, which sit above `=`/`⊨` (50).
scoped notation:60 p:61 " ≐ " q:61 => Accordion.Formula.atom (Atom.pathEq p q)
scoped notation:60 "Lin " p:61 => Accordion.Formula.atom (Atom.pathIsLin p)
scoped notation:60 τ:61 " ⊢ " p " ⇝ " l:61 => Accordion.Formula.atom (Atom.treeWalk p τ l)
scoped notation:60 τ:61 " ∶ " h:61 => Accordion.Formula.atom (Atom.treeShape τ h)
scoped notation:60 s:61 " ≐ " s':61 => Accordion.Formula.atom (Atom.setEq s s')
scoped notation:60 a:61 " ∈̇ " s:61 => Accordion.Formula.atom (Atom.setMem a s)

/-- A TWE model: an assignment to the variables of each sort (Fig. 5). -/
structure Model (Γ : Type) (V : Vars) where
  σName : V.Name → Γ
  σComp : V.Comp → Accordion.Component Γ
  σPath : V.Path → Accordion.Path Γ
  σLoc  : V.Loc → Accordion.Path Γ
  σSet  : V.Set → Finset Γ
  θ     : V.Tree → FileTree.Focus Γ

variable {Γ : Type} {V : Vars}

namespace Model

def setName [DecidableEq V.Name] (m : Model Γ V) (x : V.Name) (a : Γ) : Model Γ V :=
  { m with σName := fun y => if y = x then a else m.σName y }

def setComp [DecidableEq V.Comp] (m : Model Γ V) (x : V.Comp) (c : Accordion.Component Γ) :
    Model Γ V :=
  { m with σComp := fun y => if y = x then c else m.σComp y }

def setPath [DecidableEq V.Path] (m : Model Γ V) (x : V.Path) (p : Accordion.Path Γ) :
    Model Γ V :=
  { m with σPath := fun y => if y = x then p else m.σPath y }

def setLoc [DecidableEq V.Loc] (m : Model Γ V) (x : V.Loc) (p : Accordion.Path Γ) :
    Model Γ V :=
  { m with σLoc := fun y => if y = x then p else m.σLoc y }

def setSet [DecidableEq V.Set] (m : Model Γ V) (x : V.Set) (s : Finset Γ) : Model Γ V :=
  { m with σSet := fun y => if y = x then s else m.σSet y }

scoped macro:max (name := setNameNotation) m:term:max noWs "[" x:term " ↦ " a:term "]" : term => `(Model.setName $m $x $a)
scoped macro:max (name := setCompNotation) m:term:max noWs "[" x:term " ↦ " c:term "]" : term => `(Model.setComp $m $x $c)
scoped macro:max (name := setPathNotation) m:term:max noWs "[" x:term " ↦ " p:term "]" : term => `(Model.setPath $m $x $p)
scoped macro:max (name := setLocNotation) m:term:max noWs "[" x:term " ↦ " p:term "]" : term => `(Model.setLoc $m $x $p)
scoped macro:max (name := setSetNotation) m:term:max noWs "[" x:term " ↦ " s:term "]" : term => `(Model.setSet $m $x $s)

end Model

variable [Ord Γ]

namespace Model

def evalName (m : Model Γ V) : Name Γ V → Γ
  | .name a => a
  | .var x => m.σName x

def evalComponent (m : Model Γ V) : Component Γ V → Accordion.Component Γ
  | .empty => .empty
  | .self => .self
  | .parent => .parent
  | .name a => .name (m.evalName a)
  | .var x => m.σComp x

/-- The path a path term denotes in a model (Fig. 5). -/
def evalPath (m : Model Γ V) : Path Γ V → Accordion.Path Γ
  | .nil => .nil
  | .init b => .init (m.evalComponent b)
  | .join p q => m.evalPath p ++ m.evalPath q
  | .loc l => m.σLoc l
  | .var x => m.σPath x
  | .norm p => (m.evalPath p).norm

/-- The focus a tree term denotes in a model, if any (Fig. 5). -/
def evalTree (m : Model Γ V) : Tree V → Option (FileTree.Focus Γ)
  | .var x => some (m.θ x)
  | .file => some (.tree .file)
  | .emptyDirc => some (.tree (.dirc ∅))
  | .abst => some .abst
  | .select τ l => do
      let f ← m.evalTree τ
      let (_, f') ← f.resolve (m.σLoc l)
      some f'
  | .update τ l τ' => do
      let .tree τ'' ← m.evalTree τ | none
      let (C, _) ← FileTree.resolve (m.σLoc l) τ''
      some (.tree (← C.fill (← m.evalTree τ')))

/-- The set of names a set term denotes in a model, if any (Fig. 5). -/
def evalNameSet [DecidableEq Γ] (m : Model Γ V) :
    Set Γ V → Option (Finset Γ)
  | .var r => some (m.σSet r)
  | .empty => some ∅
  | .insert a s => (m.evalNameSet s).map (fun s => insert (m.evalName a) s)
  | .entries τ =>
      match m.evalTree τ with
      | some (.tree (.dirc δ)) => some δ.dom
      | some (.tree .file) | some .abst => some ∅
      | none => none

/-- Satisfaction of an atom in a model (Fig. 5). -/
def satAtom [DecidableEq Γ] (m : Model Γ V) : Atom Γ V → Prop
  | .pathEq p q => m.evalPath p = m.evalPath q
  | .pathIsLin p => (m.evalPath p).Linear
  | .treeWalk p τ l =>
      match m.evalTree τ with
      | some (.tree τ') =>
          match FileTree.resolve (m.evalPath p) τ' with
          | some (C, _) => C.path = m.σLoc l
          | none => False
      | _ => False
  | .treeShape τ h =>
      match m.evalTree τ with
      | some f => f.shape = h
      | none => False
  | .setEq s s' =>
      match m.evalNameSet s, m.evalNameSet s' with
      | some l₁, some l₂ => l₁ = l₂
      | _, _ => False
  | .setMem a s =>
      match m.evalNameSet s with
      | some l => m.evalName a ∈ l
      | none => False

-- A shape atom mentions no name, so the default instance takes `Γ` from the model.
@[default_instance]
instance [DecidableEq Γ] : Sat (Model Γ V) (Atom Γ V) where
  sat := satAtom

/-- A model is well-formed when its locations are linear and its trees canonical (§4.2). -/
def WF (m : Model Γ V) : Prop :=
  (∀ l, (m.σLoc l).Linear) ∧ (∀ x, (m.θ x).Canonical)

end Model

namespace Formula

/-- A formula is satisfiable when a well-formed model satisfies it (§4.2). -/
def SAT [DecidableEq Γ] (φ : Formula Γ V) : Prop :=
  ∃ m : Model Γ V, m.WF ∧ m ⊨ φ

def iff (φ ψ : Formula Γ V) : Formula Γ V := (φ ⋏ ψ) ⋎ (∼φ ⋏ ∼ψ)

def treeWalkShape (p : Path Γ V) (τ : Tree V) (l : V.Loc) (h : Shape) : Formula Γ V :=
  (τ ⊢ p ⇝ l) ⋏ (τ[l] ∶ h)

def treeWalkNotShape (p : Path Γ V) (τ : Tree V) (l : V.Loc) (h : Shape) : Formula Γ V :=
  (τ ⊢ p ⇝ l) ⋏ ∼(τ[l] ∶ h)

end Formula

scoped infixl:51 " ⇔ " => Formula.iff
scoped notation:60 τ:61 " ⊢ " p " ⇝ " l:61 " ∶ " h:61 => Formula.treeWalkShape p τ l h
scoped notation:60 τ:61 " ⊢ " p " ⇝ " l:61 " ∶∼ " h:61 => Formula.treeWalkNotShape p τ l h

namespace Model

meta def unexpandSet (kind : Lean.Name) : Lean.PrettyPrinter.Unexpander
  | `($_ $m $x $a) =>
      return Lean.mkNode kind
        #[m, Lean.mkNode `group #[], Lean.mkAtom "[", x, Lean.mkAtom " ↦ ", a, Lean.mkAtom "]"]
  | _ => throw ()

@[scoped app_unexpander setName] meta def unexpandSetName := unexpandSet ``setNameNotation
@[scoped app_unexpander setComp] meta def unexpandSetComp := unexpandSet ``setCompNotation
@[scoped app_unexpander setPath] meta def unexpandSetPath := unexpandSet ``setPathNotation
@[scoped app_unexpander setLoc] meta def unexpandSetLoc := unexpandSet ``setLocNotation
@[scoped app_unexpander setSet] meta def unexpandSetSet := unexpandSet ``setSetNotation

end Model

end TWE

end Accordion

end
