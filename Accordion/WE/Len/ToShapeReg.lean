module

public import Accordion.WE.Len.ToLenEq
public import Accordion.WE.LenEq.ToShapeReg

@[expose] public section

namespace Accordion

namespace WE

namespace Len

variable {Γ : Type} {V : Vars}

namespace Formula

/-- The reduction of WE + LEN to WE + SHAPE + REG (§5.2). -/
@[grind]
def toShapeReg [Inhabited Γ] (φ : Formula Γ V) :
    ShapeReg.Formula (LenEq.ToShapeReg.Alphabet Γ) (LenEq.ToShapeReg.Vars (V.Letter ⊕ V.Word)) :=
  LenEq.Formula.toShapeReg (toLenEq φ)

@[grind =]
theorem toShapeReg_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    [Inhabited Γ] (φ : Formula Γ V) :
    ShapeReg.Formula.SAT (toShapeReg φ) ↔ SAT φ := by
  grind only [toShapeReg, LenEq.Formula.toShapeReg_equisat (toLenEq φ),
    toLenEq_equisat]

end Formula

end Len

end WE

end Accordion

end
