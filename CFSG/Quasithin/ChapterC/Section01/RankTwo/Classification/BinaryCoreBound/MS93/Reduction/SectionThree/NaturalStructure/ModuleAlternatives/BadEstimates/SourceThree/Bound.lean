module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.ActionControl.SourceCalculation

/-!
# The binary bad-case bound from MS93 (3.3)

The three actual moving-layer calculations establish
[Z_a',Y] ≤ [X_a,X_a'] ⊔ [X_a ∩ Q_a',Y] for every critical pair, its
penultimate vertex t, and every Y ≤ Q_t ∩ C([Z_a,Z_a']). This module
exports their completed assembly for the bad-case estimates.

The doubled and central branches put the displacement in [X_a,X_a'];
the outer branch retains that commutator in the joined target. All model,
action and displacement premises are discharged by the branch proofs.
Printed (3.3) states alternatives under failure of the containment; here
the containment is proved directly under the three binary BadCase models.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), notation (3.0), p.859; (3.2)(iii)–(v), p.863; (3.3), pp.866–868.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The literal source-(3.3) containment in every binary bad branch,
with the original centralizer, orientation and penultimate-path condition.
No additional action, displacement or Frattini hypothesis is required. -/
theorem badCase_source33Bound (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hbad : BadCase source) :
    Source33Bound R geometry :=
  SourceCalculation.badCase_source33Bound source geometry hb hbad

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
