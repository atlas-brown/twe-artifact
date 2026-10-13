module

public import Accordion.WE.Walk
public import Accordion.TWE

@[expose] public section

namespace Accordion

namespace WE

namespace Walk

namespace ToTWE

def Vars (V : Walk.Vars) : TWE.Vars where
  Name := Empty
  Comp := Empty
  Path := V.Path
  Loc := V.Loc
  Tree := V.Tree
  Set := Empty

end ToTWE

namespace Path

def toTWE : Path Γ V → TWE.Path Γ (ToTWE.Vars V)
  | .nil => .nil
  | .letter a => .init (.name (.name a))
  | .var x => .var x
  | .loc l => .loc l
  | .concat p q => toTWE p ++ toTWE q

end Path

namespace Atom

open scoped TWE in
def toTWE : Atom Γ V → TWE.Formula Γ (ToTWE.Vars V)
  | .pathEq p q => p.toTWE ≐ q.toTWE
  | .treeWalk p τ l => .var τ ⊢ p.toTWE ⇝ l

end Atom

end Walk

end WE

end Accordion

end
