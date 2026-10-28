module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.SplitAndCentral.Split
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation.SplitAndCentral.Central

/-!
# MS93 (3.3) bounds for the doubled and central moving layers

The two branch calculations prove displacement bounds for the actual marked
models. Here we construct the literal conjugation action of
Q_t ∩ C([Z_a,Z_a']) on X_a'/[Z_a,Z_a'] and apply the exact quotient criterion
in reverse. This gives [Z_a',Y] ≤ [X_a,X_a'] ⊔ [X_a ∩ Q_a',Y] for every
permitted Y, preserving the source orientation and the penultimate vertex.

Both bounds depend only on the local source, positive critical distance and
the respective moving-layer model. All action and displacement premises are
discharged. The leaf proofs establish the branch calculations directly;
the failure alternatives in printed (3.3) are not assumed as a containment.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation (3.0), p.859; (3.2)(iii),(iv), p.863; (3.3), pp.866–868.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The literal source-(3.3) bound for two natural copies with their common
marking, with no additional action or critical-image premise. -/
theorem Split.source33Bound (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hmodel : SplitDouble source) :
    Source33Bound R geometry := by
  intro a ha a' hc t hat hpath Y hY
  let := SourceThree.critical_Z_quotient_normal a a'
  obtain ⟨action, hformula⟩ := SourceThree.exists_centralizingActors_action a a' t hat
  exact (bound_iff_quotient_displacement source geometry hb a ha a' hc t hat Y hY
    action hformula).mpr
      (Split.quotient_displacement source geometry hb hmodel a ha a' hc t hat hpath
        Y hY action hformula)

/-- The literal source-(3.3) bound for the natural central extension,
retaining its exact order-two kernel in the branch calculation. -/
theorem Central.source33Bound (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hmodel : CentralExtension source) :
    Source33Bound R geometry := by
  intro a ha a' hc t hat hpath Y hY
  let := SourceThree.critical_Z_quotient_normal a a'
  obtain ⟨action, hformula⟩ := SourceThree.exists_centralizingActors_action a a' t hat
  exact (bound_iff_quotient_displacement source geometry hb a ha a' hc t hat Y hY
    action hformula).mpr
      (Central.quotient_displacement source geometry hb hmodel a ha a' hc t hat hpath
        Y hY action hformula)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.SourceCalculation
