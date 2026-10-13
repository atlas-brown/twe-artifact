module

public import Accordion.FileTree

@[expose] public section

namespace Accordion

namespace FileTree

inductive Frames (Γ : Type) where
  | nil
  | push (w : Frames Γ) (δ : Entries Γ (FileTree Γ)) (a : Γ)

/-- A zipper: a focus together with the frames above it (§3.3). -/
structure Zipper (Γ : Type) where
  frames : Frames Γ
  focus : Focus Γ

variable {Γ : Type} [Ord Γ]

namespace Frames

def ctx : Frames Γ → Ctx Γ
  | .nil => .hole
  | .push w δ a => (ctx w).compose (.node δ a .hole)

end Frames

namespace Zipper

def zip (τ : FileTree Γ) : Zipper Γ := ⟨.nil, .tree τ⟩

def down (a : Γ) (z : Zipper Γ) : Option (Zipper Γ) :=
  match z.focus with
  | .tree (.dirc δ) =>
      match δ[a]? with
      | some τ => some ⟨.push z.frames (δ.erase a) a, .tree τ⟩
      | none => some ⟨.push z.frames δ a, .abst⟩
  | _ => none

def up (z : Zipper Γ) : Zipper Γ :=
  match z.frames, z.focus with
  | .nil, f => ⟨.nil, f⟩
  | .push w δ a, .tree τ => ⟨w, .tree (.dirc (δ.insert a τ))⟩
  | .push w δ _, .abst => ⟨w, .tree (.dirc δ)⟩

def move (q : Component Γ) (z : Zipper Γ) : Option (Zipper Γ) :=
  match z.focus with
  | .tree (.dirc _) =>
      match q with
      | .name a => z.down a
      | .parent => some z.up
      | .self => some z
      | .empty => some z
  | _ => none

/-- Move a zipper along a path (Fig. 3). -/
def traverse : Path Γ → Zipper Γ → Option (Zipper Γ)
  | .nil, z => some z
  | .app p q, z => (traverse p z).bind (move q)

def Canonical (z : Zipper Γ) : Prop := z.frames.ctx.Canonical ∧ z.focus.Canonical

end Zipper

/-- Resolve a path in a file tree, to the context and focus it reaches (Fig. 3). -/
def resolve (p : Path Γ) (τ : FileTree Γ) : Option (Ctx Γ × Focus Γ) :=
  (Zipper.traverse p (Zipper.zip τ)).map (fun z => (z.frames.ctx, z.focus))

namespace Focus

def resolve (p : Path Γ) : Focus Γ → Option (Ctx Γ × Focus Γ)
  | .tree τ => FileTree.resolve p τ
  | .abst => match p with
    | .nil => some (.hole, .abst)
    | .app _ _ => none

end Focus

end FileTree

end Accordion

end
