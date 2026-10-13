module

public import Accordion.WE.Len.ToLenEq
public import Accordion.WE.LenEq.ToNorm

@[expose] public section

namespace Accordion

namespace WE

namespace Len

variable {Γ : Type} {V : Vars}

namespace Formula

/-- The reduction of WE + LEN to WE + NORM (§5.1). -/
@[grind]
def toNorm [Inhabited Γ] (φ : Formula Γ V) :
    Norm.Formula Γ (LenEq.ToNorm.Var (V.Letter ⊕ V.Word)) :=
  LenEq.Formula.toNorm (toLenEq φ)

@[grind =]
theorem toNorm_equisat [Inhabited Γ] (φ : Formula Γ V) :
    Norm.Formula.SAT (toNorm φ) ↔ SAT φ := by
  grind only [toNorm, LenEq.Formula.toNorm_equisat, toLenEq_equisat]

end Formula

end Len

end WE

end Accordion

end
