module

public import Theory.SpecificGroups.Tits.FiveFrobenius
public import Theory.ElementaryAbelian.AbelianNormalClosure
import all Theory.SpecificGroups.Tits.FiveFrobenius
import all Theory.SpecificGroups.Tits.FiveFrobenius.Subgroups

/-!
# Group facts for the five-local displacement calculation

The certified generators have exponent five, and the order-24 complement acts
regularly on the 24 nonidentity kernel elements. Its quaternion square has
order two and lies in the literal transported complement.

The private imports intentionally access the subgroup closures and their
Parrott pullbacks in this internal extension of the Tits word proofs. Only
the resulting group facts are exported; the existing public boundaries are
preserved. Source and word conventions: ATLAS TF42G1-max8W1, as documented
in FiveFrobenius/Words and FiveFrobenius/Subgroups.
-/

open Subgroup
open scoped IsMulCommutative

namespace Representation.TitsFrobeniusDisplacement

private instance kernel_elementary : IsElementaryAbelian 5 Tits.FiveFrobenius.kernel := by
  let : IsMulCommutative (closure ({Tits.FiveFrobenius.v, Tits.FiveFrobenius.u} : Set Tits.Atlas1600Group)) :=
    Tits.FiveFrobenius.kernel_commutative
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x (rfl | rfl)
  · exact Tits.FiveFrobenius.v_fifth
  · exact Tits.FiveFrobenius.u_fifth

/-- The certified five-kernel is elementary abelian, on the Parrott carrier. -/
public theorem fiveKernel_elementary : IsElementaryAbelian 5 Tits.fiveKernel := by
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro k
  apply Subtype.ext
  apply Tits.parrottFiniteImageEquiv.injective
  change Tits.parrottFiniteImageEquiv ((k : Tits.ParrottGroup) ^ 5) =
    Tits.parrottFiniteImageEquiv 1
  rw [map_pow, map_one]
  exact elemPow_eq_one_of_isElementaryAbelian (A := Tits.FiveFrobenius.kernel) _ k.property

/-- The actual complement is transitive on nonidentity kernel elements. -/
public theorem five_transitive (x y : Tits.fiveKernel) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ g : normalizer (Tits.fiveKernel : Set Tits.ParrottGroup),
      Tits.fiveKernel.normalizerMonoidHom g x = y := by
  classical
  let n : Tits.fiveComplement →* normalizer (Tits.fiveKernel : Set Tits.ParrottGroup) :=
    Subgroup.inclusion Tits.fiveComplement_normalizes
  let a : Tits.fiveComplement →* MulAut Tits.fiveKernel :=
    Tits.fiveKernel.normalizerMonoidHom.comp n
  let f : Tits.fiveComplement → {k : Tits.fiveKernel // k ≠ 1} :=
    fun c => ⟨a c x, fun h => hx ((a c).injective (h.trans (map_one (a c)).symm))⟩
  have hf : Function.Injective f := by
    intro c d h
    have he : a c x = a d x := congrArg Subtype.val h
    have he' : a (d⁻¹ * c) x = x := by
      rw [map_mul, map_inv]
      change (a d).symm (a c x) = x
      rw [he]
      exact (a d).symm_apply_apply x
    have hone : d⁻¹ * c = 1 := by
      by_contra hn
      exact hx (Tits.fiveComplement_free _ hn x (congrArg Subtype.val he'))
    exact (inv_mul_eq_one.mp hone).symm
  have hcard : Nat.card {k : Tits.fiveKernel // k ≠ 1} ≤ Nat.card Tits.fiveComplement := by
    let : Fintype Tits.fiveKernel := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      ← Nat.card_eq_fintype_card, Tits.fiveKernel_card, Tits.fiveComplement_card]
    decide
  obtain ⟨c, hc⟩ := (hf.bijective_of_nat_card_le hcard).surjective ⟨y, hy⟩
  exact ⟨n c, congrArg Subtype.val hc⟩

private theorem r_square_ne : Tits.FiveFrobenius.r ^ 2 ≠ 1 := by
  intro h
  have hh := congrArg (fun g : Tits.Atlas1600Group => g.val (2 : Fin 1600)) h
  change (Tits.FiveFrobenius.r.val ^ 2) 2 = 2 at hh
  rw [Tits.FiveFrobenius.r_val] at hh
  exact (by decide +kernel : (Tits.FiveFrobenius.rp ^ 2) (2 : Fin 1600) ≠ 2) hh

/-- The literal quaternion square, transported to Parrott, has order two. -/
public theorem inverter_order : orderOf (Tits.parrottFiniteImageEquiv.symm
    (Tits.FiveFrobenius.r ^ 2)) = 2 := by
  rw [Tits.parrottFiniteImageEquiv.symm.orderOf_eq]
  apply orderOf_eq_prime_iff.mpr
  constructor
  · rw [← pow_mul]
    exact Tits.FiveFrobenius.r_fourth
  · exact r_square_ne

/-- The literal quaternion square belongs to the transported complement. -/
public theorem inverter_mem : Tits.parrottFiniteImageEquiv.symm (Tits.FiveFrobenius.r ^ 2)
    ∈ Tits.fiveComplement := by
  change Tits.parrottFiniteImageEquiv (Tits.parrottFiniteImageEquiv.symm
    (Tits.FiveFrobenius.r ^ 2)) ∈ Tits.FiveFrobenius.complement
  rw [Tits.parrottFiniteImageEquiv.apply_symm_apply]
  exact pow_mem (subset_closure (by simp)) 2

end Representation.TitsFrobeniusDisplacement
