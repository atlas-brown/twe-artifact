module

public import Accordion.TWE.Fresh

@[expose] public section

namespace Accordion

namespace TWE

/-- The variable record in which every sort is `α`. -/
def Vars.ofType (α : Type) : Vars where
  Name := α
  Comp := α
  Path := α
  Loc := α
  Tree := α
  Set := α

instance (α : Type) [DecidableEq α] : Vars.Comparable (Vars.ofType α) where
  name := inferInstanceAs (DecidableEq α)
  comp := inferInstanceAs (DecidableEq α)
  path := inferInstanceAs (DecidableEq α)
  loc := inferInstanceAs (DecidableEq α)
  set := inferInstanceAs (DecidableEq α)
  tree := inferInstanceAs (DecidableEq α)

instance (α : Type) [Accordion.Fresh α] : Vars.Fresh (Vars.ofType α) where
  name := inferInstanceAs (Accordion.Fresh α)
  comp := inferInstanceAs (Accordion.Fresh α)
  path := inferInstanceAs (Accordion.Fresh α)
  loc := inferInstanceAs (Accordion.Fresh α)
  set := inferInstanceAs (Accordion.Fresh α)

end TWE

end Accordion

end
