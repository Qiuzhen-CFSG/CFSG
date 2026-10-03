module

public import Stellmacher.Recognition.Parrott.SecondCentralizer
public import Stellmacher.Recognition.Parrott.NormalizerCoreOmegaElementaryQuotient

/-!
# Products involving the z-class in the second centralizer

The actual two-core U of C_G(v) is the omega subgroup of the second normalizer
core. Its squares lie in F, so its fourth powers are trivial. Outside-core
fusion forces every z-class involution in C_G(v) into U. The product of such
an involution with any square-one element has square in U, hence eighth power
one. These statements retain the supplied normalizer and elementary data.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§4, pp.682–683, and §6, printed p.684, Verification of VI(i).
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

/-- The actual second-centralizer two-core has fourth power one: its squares
lie in the supplied elementary subgroup F. -/
public theorem ParrottSecondCentralizerData.core_fourth_power_eq_one
    (c : ParrottSecondCentralizerData n)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (a : pCore 2 (centralizer ({n.v} : Set G))) : a ^ 4 = 1 := by
  have ha : ((a : centralizer ({n.v} : Set G)) : G) ∈
      (pCore 2 (centralizer ({n.v} : Set G))).map
        (centralizer ({n.v} : Set G)).subtype := mem_map_of_mem _ a.property
  rw [c.core_eq] at ha
  have ha2 := e.normalizer_omega_square_mem_elementary h hN
    n.sylow_lt_normalizer n.Q n.core_fixed_le_derived _ ha
  let : IsElementaryAbelian 2 e.F := e.elementary
  have ha4 := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ ha2
  apply Subtype.ext
  apply Subtype.ext
  change (((a : centralizer ({n.v} : Set G)) : G)) ^ 4 = 1
  simpa only [← pow_mul] using ha4

/-- Multiplying an involution from the z-class by a square-one element in
the second centralizer gives eighth power one. Outside-core fusion puts the
first involution in the core, so the square of the product lies there too. -/
public theorem ParrottSecondCentralizerData.involution_product_eighth_power
    (c : ParrottSecondCentralizerData n)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (a b : centralizer ({n.v} : Set G))
    (ha : orderOf (a : G) = 2) (haz : IsConj (a : G) z) (hb : b ^ 2 = 1) :
    (a * b) ^ 8 = 1 := by
  let C := centralizer ({n.v} : Set G)
  let U := pCore 2 C
  have haU : a ∈ U := by
    by_contra hnot
    have hnot' : (a : G) ∉ U.map C.subtype := by
      rintro ⟨u, hu, he⟩
      exact hnot ((Subtype.ext he : u = a) ▸ hu)
    exact n.not_isConj (haz.symm.trans (c.outside_core_fusion _ a.property ha hnot').symm)
  have hqa : QuotientGroup.mk' U a = 1 := (QuotientGroup.eq_one_iff a).mpr haU
  have hp : (a * b) ^ 2 ∈ U := by
    apply (QuotientGroup.eq_one_iff (N := U) _).mp
    change QuotientGroup.mk' U ((a * b) ^ 2) = 1
    rw [map_pow, map_mul, hqa, one_mul, ← map_pow,
      hb, map_one]
  have hh := congrArg U.subtype (c.core_fourth_power_eq_one h hN ⟨(a * b) ^ 2, hp⟩)
  change ((a * b) ^ 2) ^ 4 = 1 at hh
  exact (by simpa only [← pow_mul] using hh)

end Stellmacher.Recognition
