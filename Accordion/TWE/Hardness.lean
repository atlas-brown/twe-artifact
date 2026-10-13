module

public import Accordion.WE.Len.ToNorm
public import Accordion.WE.Len.ToShapeReg
public import Accordion.WE.Len.ToTWE
public import Accordion.WE.Len.ToWalk

@[expose] public section

namespace Accordion

namespace WE

variable {Γ : Type} {V : Vars} [Inhabited Γ]

namespace Len

/-- WE + LEN reduces to WE + NORM (§5.1, Theorem 2). -/
theorem toNorm_equisat (φ : Formula Γ V) :
    Norm.Formula.SAT (Formula.toNorm φ) ↔ Formula.SAT φ :=
  Formula.toNorm_equisat φ

/-- WE + LEN reduces to WE + WALK (§5.1, Theorem 3). -/
theorem toWalk_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    (φ : Formula Γ V) :
    Walk.Formula.SAT (Formula.toWalk φ) ↔ Formula.SAT φ :=
  Formula.toWalk_equisat φ

/-- WE + LEN reduces to WE + SHAPE + REG (§5.2). -/
theorem toShapeReg_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    (φ : Formula Γ V) :
    ShapeReg.Formula.SAT (Formula.toShapeReg φ) ↔ Formula.SAT φ :=
  Formula.toShapeReg_equisat φ

/-- WE + LEN reduces to TWE (§5). -/
theorem toTWE_equisat [Ord Γ] [DecidableEq Γ] (φ : Formula Γ V) :
    TWE.Formula.SAT (Formula.toTWE φ) ↔ Formula.SAT φ :=
  Formula.toTWE_equisat φ

/-- WE + LEN reduces to TWE through WE + NORM (§5). -/
theorem toTWE_toNorm_equisat [Ord Γ] [DecidableEq Γ] (φ : Formula Γ V) :
    TWE.Formula.SAT (Norm.Formula.toTWE (Formula.toNorm φ)) ↔ Formula.SAT φ :=
  Formula.toTWE_toNorm_equisat φ

/-- WE + LEN reduces to TWE through WE + WALK (§5). -/
theorem toTWE_toWalk_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    (φ : Formula Γ V) :
    TWE.Formula.SAT (Walk.Formula.toTWE (Formula.toWalk φ)) ↔ Formula.SAT φ :=
  Formula.toTWE_toWalk_equisat φ

end Len

end WE

end Accordion

end
