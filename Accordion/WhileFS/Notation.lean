module

public import Accordion.WhileFS
public import Accordion.Path.StrictPrefix

@[expose] public section

namespace Accordion

instance {Γ X : Type} : EmptyCollection (Store Γ X) := ⟨fun _ => none⟩

namespace WhileFS

scoped instance {Γ X : Type} : Coe (Path Γ) (Expr Γ X) := ⟨fun p => .val (.path p)⟩

scoped instance {Γ : Type} : HDiv (Path Γ) Γ (Path Γ) := ⟨fun p a => .app p (.name a)⟩

scoped instance {Γ : Type} (q : Path Γ) (a : Γ) : q.IsStrictPrefix (q / a) := .self _

scoped instance {Γ : Type} {q p : Path Γ} [h : q.IsStrictPrefix p] (a : Γ) :
    q.IsStrictPrefix (p / a) := .step _ h

scoped notation:max p "/‥" => Path.app p Component.parent

scoped infixr:35 " ;; " => Command.seq

end WhileFS

end Accordion

end
