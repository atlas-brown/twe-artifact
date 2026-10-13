module

public import Accordion.WE.Len.ToNorm
public import Accordion.WE.Len.ToWalk
public import Accordion.WE.Norm.ToTWE
public import Accordion.WE.Walk.ToTWE

@[expose] public section

namespace Accordion

namespace WE

namespace Len

variable {Γ : Type} {V : Vars}

namespace Formula

/-- The reduction of WE + LEN to TWE (§5). -/
@[grind]
def toTWE [Inhabited Γ] (φ : Formula Γ V) :
    TWE.Formula Γ (Norm.ToTWE.Vars (LenEq.ToNorm.Var (V.Letter ⊕ V.Word))) :=
  Norm.Formula.toTWE (toNorm φ)

theorem toTWE_toNorm_equisat [Ord Γ] [DecidableEq Γ] [Inhabited Γ] (φ : Formula Γ V) :
    TWE.Formula.SAT (Norm.Formula.toTWE (toNorm φ)) ↔ SAT φ := by
  grind only [Norm.Formula.toTWE_equisat, toNorm_equisat]

theorem toTWE_toWalk_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    [Inhabited Γ] (φ : Formula Γ V) :
    TWE.Formula.SAT (Walk.Formula.toTWE (toWalk φ)) ↔ SAT φ := by
  grind only [Walk.Formula.toTWE_equisat, toWalk_equisat]

@[grind =]
theorem toTWE_equisat [Ord Γ] [DecidableEq Γ] [Inhabited Γ] (φ : Formula Γ V) :
    TWE.Formula.SAT (toTWE φ) ↔ SAT φ := by
  grind only [toTWE, toTWE_toNorm_equisat]

end Formula

end Len

end WE

end Accordion

end
