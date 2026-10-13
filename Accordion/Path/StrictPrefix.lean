module

public import Accordion.Path

@[expose] public section

namespace Accordion

class inductive Path.IsStrictPrefix {Γ : Type} (q : Path Γ) : Path Γ → Prop
  | self (c : Component Γ) : IsStrictPrefix q (q.app c)
  | step {p : Path Γ} (c : Component Γ) (h : IsStrictPrefix q p) : IsStrictPrefix q (p.app c)

attribute [instance] Path.IsStrictPrefix.self

instance {Γ : Type} {q p : Path Γ} [h : q.IsStrictPrefix p] (c : Component Γ) :
    q.IsStrictPrefix (p.app c) := .step c h

end Accordion

end
