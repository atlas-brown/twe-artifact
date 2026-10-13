module

public import Accordion.WE.Len.ToLenEq.Properties

@[expose] public section

namespace Accordion

namespace WE

namespace Len

open scoped Accordion.Formula
open ToLenEq

variable {Γ : Type} {V : WE.Vars}

namespace Formula

def toLenEq [Inhabited Γ] (φ : Formula Γ V) : LenEq.Formula Γ (ToLenEq.Vars V) :=
  guards (letterVars φ) ⋏ φ.bind Atom.toLenEq

@[grind =]
theorem toLenEq_equisat [Inhabited Γ] (φ : Formula Γ V) :
    LenEq.Formula.SAT (toLenEq φ) ↔ SAT φ :=
  guards_bind_toLenEq_equisat φ

end Formula

end Len

end WE

end Accordion

end
