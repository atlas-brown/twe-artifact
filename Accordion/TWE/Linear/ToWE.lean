module

public import Accordion.TWE.Linear.ToWE.Properties.RewriteWalks
public import Accordion.TWE.Linear.ToWE.Properties.CaseUpdates
public import Accordion.TWE.Linear.ToWE.Properties.ReifyShapes

@[expose] public section

namespace Accordion

namespace TWE

namespace Linear

variable {Γ : Type} {V : TWE.Vars}

namespace ToWE

open Linear.ToWE.Atom (WalksRewritten EntriesNamed EntriesRewritten UpdatesEliminated
  EntriesEliminated SetsEncoded)

theorem rewriteWalks_equisat [Ord Γ] [DecidableEq Γ] [Nonempty Γ] (φ : TWE.Formula Γ V) :
    Guess.SAT (rewriteWalks φ) ↔ TWE.Linear.Formula.SAT φ :=
  SAT_rewriteWalks_iff φ

theorem rewriteWalks_mem_walksRewritten (φ : TWE.Formula Γ V) : rewriteWalks φ ∈ WalksRewritten :=
  allAtoms_walksRewritten_rewriteWalks φ

theorem nameEntries_equisat [Ord Γ] [DecidableEq Γ] [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (D : Guess (Conj Γ V)) (hD : D ∈ WalksRewritten) :
    Guess.SAT (D.flatMap (rewriteAtoms nameEntries)) ↔ Guess.SAT D :=
  flatMap_equisat_of_mem
    (fun β _ => rewriteAtoms_equisat (fun α _ hα => nameEntries_satPreserving α hα) β) hD

theorem nameEntries_mem_entriesNamed [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (D : Guess (Conj Γ V)) (hD : D ∈ WalksRewritten) :
    D.flatMap (rewriteAtoms nameEntries) ∈ EntriesNamed :=
  flatMap_mem_fragment (fun β _ => rewriteAtoms_nameEntries_mem_entriesNamed β) hD

theorem caseUpdates_equisat [Ord Γ] [DecidableEq Γ] [TWE.Vars.Comparable V]
    (D : Guess (Conj Γ V)) (hD : D ∈ EntriesNamed) :
    Guess.SAT (D.flatMap (rewriteConj caseUpdates)) ↔ Guess.SAT D :=
  flatMap_equisat_of_mem (fun β _ => run_caseUpdates_equisat β _) hD

theorem caseUpdates_mem_entriesNamed [TWE.Vars.Comparable V] (D : Guess (Conj Γ V))
    (hD : D ∈ EntriesNamed) : D.flatMap (rewriteConj caseUpdates) ∈ EntriesNamed :=
  flatMap_mem_fragment (fun β hβ => run_caseUpdates_mem_entriesNamed β hβ _) hD

theorem caseUpdates_updatesDefined [Ord Γ] [DecidableEq Γ] [TWE.Vars.Comparable V]
    (D : Guess (Conj Γ V)) : Guess.UpdatesDefined (D.flatMap (rewriteConj caseUpdates)) :=
  Guess.updatesDefined_flatMap fun β _ => run_caseUpdates_updatesDefined β _

theorem rewriteEntriesAtom_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (D : Guess (Conj Γ V))
    (hdefined : D.UpdatesDefined) :
    Guess.SAT (D.flatMap (rewriteAtoms rewriteEntriesAtom)) ↔ Guess.SAT D :=
  flatMap_rewriteAtoms_equisat_of_updatesDefined
    (fun α _ hα => rewriteEntriesAtom_satPreserving α hα) allAtoms_updates_subset_rewriteEntriesAtom
    D hdefined

theorem rewriteEntriesAtom_mem_entriesRewritten [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (D : Guess (Conj Γ V)) (hD : D ∈ EntriesNamed) :
    D.flatMap (rewriteAtoms rewriteEntriesAtom) ∈ EntriesRewritten :=
  flatMap_mem_fragment rewriteAtoms_rewriteEntriesAtom_mem_entriesRewritten hD

theorem rewriteEntriesAtom_updatesDefined [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ]
    [DecidableEq Γ] [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (D : Guess (Conj Γ V))
    (hdefined : D.UpdatesDefined) :
    Guess.UpdatesDefined (D.flatMap (rewriteAtoms rewriteEntriesAtom)) :=
  updatesDefined_flatMap_rewriteAtoms
    (fun α _ hα => rewriteEntriesAtom_satPreserving α hα) allAtoms_updates_subset_rewriteEntriesAtom
    D hdefined

theorem rewriteShapeAtom_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (D : Guess (Conj Γ V))
    (hdefined : D.UpdatesDefined) :
    Guess.SAT (D.flatMap (rewriteAtoms rewriteShapeAtom)) ↔ Guess.SAT D :=
  flatMap_rewriteAtoms_equisat_of_updatesDefined
    (fun α _ hα => rewriteShapeAtom_satPreserving α hα) allAtoms_updates_subset_rewriteShapeAtom
    D hdefined

theorem rewriteShapeAtom_mem_updatesEliminated [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (D : Guess (Conj Γ V)) (hD : D ∈ EntriesRewritten) :
    D.flatMap (rewriteAtoms rewriteShapeAtom) ∈ UpdatesEliminated :=
  flatMap_mem_fragment rewriteAtoms_rewriteShapeAtom_mem_updatesEliminated hD

theorem eliminateEntries_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (D : Guess (Conj Γ V))
    (hD : D ∈ UpdatesEliminated) :
    Guess.SAT (D.flatMap (rewriteConj eliminateEntries)) ↔ Guess.SAT D :=
  flatMap_equisat_of_mem
    (fun β hβ => run_eliminateEntries_equisat β hβ (TWE.Free.Subset.refl _)) hD

theorem eliminateEntries_mem_entriesEliminated [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (D : Guess (Conj Γ V)) (hD : D ∈ UpdatesEliminated) :
    D.flatMap (rewriteConj eliminateEntries) ∈ EntriesEliminated :=
  flatMap_mem_fragment (fun β hβ => run_eliminateEntries_mem_entriesEliminated β hβ _) hD

theorem rewriteSetDisequality_equisat [Ord Γ] [DecidableEq Γ] [TWE.Vars.Comparable V]
    [TWE.Vars.Fresh V] (D : Guess (Conj Γ V)) (hD : D ∈ EntriesEliminated) :
    Guess.SAT (D.flatMap (rewriteAtoms rewriteSetDisequality)) ↔ Guess.SAT D :=
  flatMap_equisat_of_mem
    (fun β _ => rewriteAtoms_equisat (fun α _ hα => rewriteSetDisequality_satPreserving α hα) β) hD

theorem rewriteSetDisequality_mem_entriesEliminated [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (D : Guess (Conj Γ V)) (hD : D ∈ EntriesEliminated) :
    D.flatMap (rewriteAtoms rewriteSetDisequality) ∈ EntriesEliminated :=
  flatMap_mem_fragment rewriteAtoms_rewriteSetDisequality_mem_entriesEliminated hD

theorem encodeSets_equisat [Ord Γ] [DecidableEq Γ] [Infinite Γ] [TWE.Vars.Comparable V]
    [TWE.Vars.Fresh V] (D : Guess (Conj Γ V)) (hD : D ∈ EntriesEliminated) :
    Guess.SAT (D.flatMap (rewriteConj encodeSets)) ↔ Guess.SAT D :=
  flatMap_equisat_of_mem (fun β hβ => run_encodeSets_equisat β hβ (TWE.Free.Subset.refl _)) hD

theorem encodeSets_mem_setsEncoded [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]
    (D : Guess (Conj Γ V)) (hD : D ∈ EntriesEliminated) :
    D.flatMap (rewriteConj encodeSets) ∈ SetsEncoded :=
  flatMap_mem_fragment (fun β hβ => run_encodeSets_mem_setsEncoded β hβ _) hD

theorem reifyShapes_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    [TWE.Vars.Comparable V] [TWE.Vars.Fresh V] (D : Guess (Conj Γ V)) (hD : D ∈ SetsEncoded) :
    (∃ ψ ∈ D.map (rewriteConj reifyShapes), WE.Formula.SAT ψ) ↔ Guess.SAT D :=
  exists_SAT_map_reifyShapes_iff hD

end ToWE

open ToWE

variable [TWE.Vars.Comparable V] [TWE.Vars.Fresh V]

namespace Formula

/-- The reduction of linear TWE to WE (§6.1). A rule that produces a disjunction of conjunctions is
a guess; disjunctions inside word formulas are kept. -/
def toWE (φ : TWE.Formula Γ V) : Guess (WE.Formula Γ (ToWE.Vars V)) :=
  rewriteWalks φ
    |>.flatMap (rewriteAtoms nameEntries)
    |>.flatMap (rewriteConj caseUpdates)
    |>.flatMap (rewriteAtoms rewriteEntriesAtom)
    |>.flatMap (rewriteAtoms rewriteShapeAtom)
    |>.flatMap (rewriteConj eliminateEntries)
    |>.flatMap (rewriteAtoms rewriteSetDisequality)
    |>.flatMap (rewriteConj encodeSets)
    |>.map (rewriteConj reifyShapes)

@[grind =_]
theorem toWE_equisat [Ord Γ] [Std.TransOrd Γ] [Std.LawfulEqOrd Γ] [DecidableEq Γ]
    [Infinite Γ] (φ : TWE.Formula Γ V) :
    (∃ ψ ∈ toWE φ, WE.Formula.SAT ψ) ↔ SAT φ := by
  have h₁ := rewriteWalks_mem_walksRewritten φ
  have h₂ := nameEntries_mem_entriesNamed _ h₁
  have h₃ := caseUpdates_mem_entriesNamed _ h₂
  have d₃ := caseUpdates_updatesDefined ((rewriteWalks φ).flatMap (rewriteAtoms nameEntries))
  have h₄ := rewriteEntriesAtom_mem_entriesRewritten _ h₃
  have d₄ := rewriteEntriesAtom_updatesDefined _ d₃
  have h₅ := rewriteShapeAtom_mem_updatesEliminated _ h₄
  have h₆ := eliminateEntries_mem_entriesEliminated _ h₅
  have h₇ := rewriteSetDisequality_mem_entriesEliminated _ h₆
  have h₈ := encodeSets_mem_setsEncoded _ h₇
  exact (reifyShapes_equisat _ h₈).trans <| (encodeSets_equisat _ h₇).trans <|
    (rewriteSetDisequality_equisat _ h₆).trans <| (eliminateEntries_equisat _ h₅).trans <|
    (rewriteShapeAtom_equisat _ d₄).trans <| (rewriteEntriesAtom_equisat _ d₃).trans <|
    (caseUpdates_equisat _ h₂).trans <| (nameEntries_equisat _ h₁).trans <|
    rewriteWalks_equisat φ

end Formula

end Linear

end TWE

end Accordion

end
