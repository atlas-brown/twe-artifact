module

public import Accordion.WE.Walk.ToTWE.Properties

@[expose] public section

namespace Accordion

namespace WE

namespace Walk

variable {Γ : Type} {V : Vars}

namespace Formula

def toTWE (φ : Formula Γ V) : TWE.Formula Γ (ToTWE.Vars V) :=
  φ.bind Atom.toTWE

@[grind =]
theorem toTWE_equisat [Ord Γ] [DecidableEq Γ] (φ : Formula Γ V) :
    TWE.Formula.SAT (toTWE φ) ↔ SAT φ :=
  bind_toTWE_equisat φ

end Formula

end Walk

end WE

end Accordion

end
