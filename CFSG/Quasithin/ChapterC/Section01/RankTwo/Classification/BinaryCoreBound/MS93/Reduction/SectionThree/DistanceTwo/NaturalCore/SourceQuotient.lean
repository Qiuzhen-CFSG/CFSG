module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.QuotientConstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.QuotientCommutators
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.QuotientOrder

/-!+# The natural core quotient from the distance-two source hypotheses

In the natural, non-Frattini branch at critical distance two, the local
critical-pair calculation gives [core,Q] ≤ U. The resulting quotient action
and its small involution displacement give |core| = 64. These two estimates
discharge the inputs of the actual core/U construction: a surjection onto
the binary natural three-space, with exact kernel U and the ambient
conjugation action through the specified SL₃(2) quotient.

The quotient has its own automorphism marking. No agreement with the
marking on U, abelianness of core, or extension estimates are assumed.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the natural branch of (3.6), printed pp.870--871, using (3.3)--(3.5).
This supplies the quotient used before the subsequent central-extension
argument establishing abelianness and agreement of the two natural modules.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The natural non-Frattini branch at distance two supplies the actual
marked core/U quotient, with no additional local estimates as hypotheses. -/
theorem exists_naturalCoreQuotient (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    Nonempty (NaturalCoreQuotient source) := by
  have hcomm := core_commutator_Q_le_U source geometry hb natural hlarge
  have hcard := core_card_eq_sixty_four source geometry hb natural hlarge hcomm
  exact exists_naturalCoreQuotient_of_local_estimates source geometry hb natural hcard hcomm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
