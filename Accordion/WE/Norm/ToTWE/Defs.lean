module

public import Accordion.WE.Norm
public import Accordion.TWE

@[expose] public section

namespace Accordion

namespace WE

namespace Norm

namespace ToTWE

def Vars (X : Type) : TWE.Vars where
  Name := Empty
  Comp := Empty
  Path := X
  Loc := Empty
  Tree := Empty
  Set := Empty

end ToTWE

namespace Path

def toTWE : Path Γ X → TWE.Path Γ (ToTWE.Vars X)
  | .nil => .nil
  | .letter a => .init (.name (.name a))
  | .var x => .var x
  | .concat p q => toTWE p ++ toTWE q
  | .norm p => .norm (toTWE p)

end Path

namespace Atom

open scoped TWE in
def toTWE : Atom Γ X → TWE.Formula Γ (ToTWE.Vars X)
  | .pathEq p q => p.toTWE ≐ q.toTWE

end Atom

end Norm

end WE

end Accordion

end
