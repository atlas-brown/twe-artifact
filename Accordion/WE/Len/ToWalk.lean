module

public import Accordion.WE.Len.ToLenEq
public import Accordion.WE.LenEq.ToWalk

@[expose] public section

namespace Accordion

namespace WE

namespace Len

variable {Γ : Type} {V : Vars}

namespace Formula

/-- The reduction of WE + LEN to WE + WALK (§5.1). -/
@[grind]
def toWalk [Inhabited Γ] (φ : Formula Γ V) :
    Walk.Formula Γ (LenEq.ToWalk.Vars Γ (ToLenEq.Vars V)) :=
  LenEq.Formula.toWalk (toLenEq φ)

@[grind =]
theorem toWalk_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [Inhabited Γ] (φ : Formula Γ V) :
    Walk.Formula.SAT (toWalk φ) ↔ SAT φ := by
  grind only [toWalk, LenEq.Formula.toWalk_equisat (toLenEq φ), toLenEq_equisat]

end Formula

end Len

end WE

end Accordion

end
