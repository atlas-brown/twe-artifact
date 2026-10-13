module

public import Accordion.WE.Norm.ToTWE.Properties

@[expose] public section

namespace Accordion

namespace WE

namespace Norm

variable {Γ X : Type}

namespace Formula

def toTWE (φ : Formula Γ X) : TWE.Formula Γ (ToTWE.Vars X) :=
  φ.bind Atom.toTWE

@[grind =]
theorem toTWE_equisat [Ord Γ] [DecidableEq Γ] (φ : Formula Γ X) :
    TWE.Formula.SAT (toTWE φ) ↔ SAT φ :=
  bind_toTWE_equisat φ

end Formula

end Norm

end WE

end Accordion

end
