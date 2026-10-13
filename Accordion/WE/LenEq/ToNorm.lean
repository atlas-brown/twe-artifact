module

public import Accordion.WE.LenEq.ToNorm.Properties

@[expose] public section

namespace Accordion

namespace WE

namespace LenEq

open scoped Accordion.Formula
open ToNorm

variable {Γ : Type} {V : WE.Vars} [IsEmpty V.Letter]

namespace Formula

def toNorm [Inhabited Γ] (φ : Formula Γ V) : Norm.Formula Γ (Var V.Word) :=
  inverseGuards (vars φ) ⋏ φ.bind Atom.toNorm

@[grind =]
theorem toNorm_equisat [Inhabited Γ] (φ : Formula Γ V) :
    Norm.Formula.SAT (toNorm φ) ↔ SAT φ :=
  inverseGuards_bind_equisat φ

end Formula

end LenEq

end WE

end Accordion

end
