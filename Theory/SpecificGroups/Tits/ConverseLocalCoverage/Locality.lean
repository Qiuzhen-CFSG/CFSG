module

public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.FirstCentralizer
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.SecondNormalizer
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!+# Genuine two-local subgroups for the Tits coverage argument

The first parabolic is the centralizer of the involution r5, hence the
normalizer of its order-two subgroup. The second is the normalizer of the
explicit nontrivial second center of the Sylow subgroup. Every two-local
is proper: simplicity would otherwise make its normal two-subgroup the
whole group, contradicting the certified ambient order.

Source: Parrott (1972), pp.672,683; the two-local convention is that of
Aschbacher–Smith, printed pp.3 and 481 of `refs/quasithin.pdf`.
-/

namespace Tits.ConverseLocalCoverage
open Subgroup ExceptionalParabolics RelativeParabolicNormalizers

/-- The marked central word is an involution, using the exact Sylow center. -/
public theorem r5_order : orderOf atlas1600R5 = 2 := by
  let z : S := ⟨atlas1600R5, atlas1600R5_mem_sylowTwo⟩
  have hz : z ∈ center S := atlas1600R5_mem_center_sylowTwo
  have hs := (atlas1600SylowTwo_mem_center_iff (z ^ 2)).mp ((center S).pow_mem hz 2)
  change atlas1600R5 ^ 2 = 1 ∨ atlas1600R5 ^ 2 = atlas1600R5 at hs
  have hsq : atlas1600R5 ^ 2 = 1 := by
    rcases hs with h | h
    · exact h
    · have he : atlas1600R5 * atlas1600R5 = atlas1600R5 * 1 := by
        simpa only [pow_two, mul_one] using h
      exact (atlas1600R5_ne_one (mul_left_cancel he)).elim
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact orderOf_eq_prime hsq atlas1600R5_ne_one

/-- The first parabolic is two-local in the ambient group. -/
public theorem first_isTwoLocal : IsTwoLocal first := by
  rw [first_eq_centralizer]
  exact Theory.GroupTheory.isTwoLocal_involution_centralizer r5_order

/-- The second parabolic is two-local in the ambient group. -/
public theorem second_isTwoLocal : IsTwoLocal second := by
  refine ⟨secondCenter, ?_, secondCenter_isPGroup,
    second_eq_normalizer_secondCenter first_eq_centralizer⟩
  intro h
  have hx : atlas1600R5 ∈ secondCenter := mem_sup_left (mem_zpowers _)
  rw [h, mem_bot] at hx
  exact atlas1600R5_ne_one hx

/-- A two-local cannot be the whole concrete simple Tits group. -/
public theorem twoLocal_ne_top (M : Subgroup Atlas1600Group) (hM : IsTwoLocal M) :
    M ≠ ⊤ := by
  obtain ⟨Q, hQ, hp, rfl⟩ := hM
  intro hn
  have hnormal : Q.Normal := normalizer_eq_top_iff.mp hn
  have htop : Q = ⊤ := hnormal.eq_bot_or_eq_top.resolve_left hQ
  have hpG : IsPGroup 2 Atlas1600Group :=
    (htop ▸ hp).of_equiv (topEquiv : (⊤ : Subgroup Atlas1600Group) ≃* Atlas1600Group)
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpG
  have hd : 3 ∣ 2 ^ n := by
    rw [← hn, atlas1600Group_card]
    norm_num
  have hf := (by decide : Nat.Prime 3).dvd_of_dvd_pow hd
  norm_num at hf

end Tits.ConverseLocalCoverage
