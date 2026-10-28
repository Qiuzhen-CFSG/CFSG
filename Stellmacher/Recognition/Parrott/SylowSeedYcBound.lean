module

public import Stellmacher.Recognition.Parrott.SylowSeedLastRelations
public import Stellmacher.Recognition.Parrott.SylowSeedOuterCentralization
public import Theory.SpecificGroups.Tits.RecognitionSylowYcBound

/-!
# The c-commutator in Parrott's last Sylow relations

The actual derived-centralizer equality bounds the outer c-image by elementary
coordinates. The normalized b-image eliminates the uv error, and the square
action gives [x²z,c]=atz directly. This proves the two-valued bound and supplies
the value required by the remaining coordinate normalization. The existing
local nonfusion selection interface is retained; no global class of x²z is
assumed.

Source: Parrott (1972), printed p.680, immediately before equation (19).
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSylowSeedData

variable {G : Type*} [Group G] [Finite G] {z : G}
  {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

public theorem yc_cases (f : ParrottSylowSeedData n false)
    (h : ParrottCentralizerHypotheses z) (hm : f.OuterMiddleRelations) :
    Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t ∨
      Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z := by
  have hz : z ≠ 1 := (orderOf_eq_prime_iff.mp h.involution).2
  obtain ⟨hb, hc, hd⟩ := f.outer_discrepancies_mem_derived h
  obtain ⟨_, ⟨ci, cj, ck, hc⟩, _⟩ :=
    f.relations.outer_image_parameters hz hm.eq16_ax hb hc hd
  exact Or.inr (f.relations.yc_of_image_parameters hz hm.eq16_ax hm.eq18_bx ci cj ck hc)

public theorem yc_selected [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (h : ParrottCentralizerHypotheses z) (f : ParrottSylowSeedData n false)
    (hm : f.OuterMiddleRelations) :
    Tits.parrottCommutator (f.x^2*z) f.c = f.a*n.t*z := by
  exact f.eq19_yc_of_alternative hns hN h hm (f.yc_cases h hm)

end Stellmacher.Recognition.ParrottSylowSeedData
