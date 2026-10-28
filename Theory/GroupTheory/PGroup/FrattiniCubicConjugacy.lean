module
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Mathlib.GroupTheory.Sylow

/-!
# Cubic automorphisms of a two-group with Frattini quotient of order eight

Burnside's basis-kernel theorem gives a two-group kernel on the Frattini
quotient. The general linear group of a binary three-space has order 168,
so nine cannot divide the automorphism group order. Consequently every
nontrivial cubic automorphism generates a Sylow three-subgroup. Sylow
conjugacy identifies two such automorphisms up to inversion.

This is the standard Burnside basis and Sylow argument used for the second
binary Ree endpoint in Aschbacher–Smith, F.1.12 and J.4.5.
-/

public section
noncomputable section
open Subgroup
namespace IsPGroup
variable {Q : Type*} [Group Q] [Finite Q]

theorem not_nine_dvd_card_mulAut_of_frattini_eight (hQ : IsPGroup 2 Q)
    (hcard : Nat.card (Q ⧸ frattini Q) = 8) : ¬9 ∣ Nat.card (MulAut Q) := by
  let _ : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  let _ : IsElementaryAbelian 2 (Q ⧸ frattini Q) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  let f := quotientAut (frattini Q)
  have hcount : Nat.card f.ker * Nat.card f.range = Nat.card (MulAut Q) := by
    rw [← index_ker]
    exact f.ker.card_mul_index
  obtain ⟨n, hn⟩ := (isPGroup_quotientAut_frattini_kernel hQ).exists_card_eq
  have hcop : Nat.Coprime 9 (Nat.card f.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 9 2).pow_right n
  have hAut : ¬9 ∣ Nat.card (MulAut (Q ⧸ frattini Q)) := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 3 hcard]
    norm_num [Fin.prod_univ_succ]
  intro h
  rw [← hcount] at h
  exact hAut ((hcop.dvd_of_dvd_mul_left h).trans f.range.card_subgroup_dvd_card)

private def cubicSylow (hQ : IsPGroup 2 Q) (hcard : Nat.card (Q ⧸ frattini Q) = 8)
    (a : MulAut Q) (ha : orderOf a = 3) : Sylow 3 (MulAut Q) := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hc : Nat.card (zpowers a) = 3 := (Nat.card_zpowers a).trans ha
  refine (IsPGroup.of_card (p := 3) (n := 1) hc).toSylow ?_
  rintro ⟨k, hk⟩
  apply hQ.not_nine_dvd_card_mulAut_of_frattini_eight hcard
  refine ⟨k, ?_⟩
  rw [← (zpowers a).card_mul_index, hc, hk]
  omega

theorem cubic_mulAut_conjugate_or_inverse_of_frattini_eight
    (hQ : IsPGroup 2 Q) (hcard : Nat.card (Q ⧸ frattini Q) = 8)
    (a b : MulAut Q) (ha : orderOf a = 3) (hb : orderOf b = 3) :
    ∃ e : MulAut Q, e * a * e⁻¹ = b ∨ e * a * e⁻¹ = b⁻¹ := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq (MulAut Q)
    (cubicSylow hQ hcard a ha) (cubicSylow hQ hcard b hb)
  have hm : e * a * e⁻¹ ∈ zpowers b := by
    have ht : a ∈ cubicSylow hQ hcard a ha := mem_zpowers a
    have hmem := Subgroup.smul_mem_pointwise_smul a (MulAut.conj e)
      (cubicSylow hQ hcard a ha : Subgroup (MulAut Q)) ht
    change e * a * e⁻¹ ∈ e • cubicSylow hQ hcard a ha at hmem
    rw [he] at hmem
    exact hmem
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp
    ((isOfFinOrder_of_finite b).mem_zpowers_iff_mem_range_orderOf.mp hm)
  have hk3 : k < 3 := by simpa only [Finset.mem_range, hb] using hk
  have hk0 : k ≠ 0 := by
    intro hk0
    have he1 : e*a*e⁻¹=1 := by simpa only [hk0, pow_zero] using heq.symm
    have ha1 : a=1 := (MulAut.conj e).injective (he1.trans (map_one _).symm)
    simp [ha1] at ha
  refine ⟨e, ?_⟩
  interval_cases k
  · exact False.elim (hk0 rfl)
  · exact Or.inl (by simpa only [pow_one] using heq.symm)
  · right
    have hb3 : b^3=1 := hb ▸ pow_orderOf_eq_one b
    have hb2 : b^2=b⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      simpa only [← pow_succ] using hb3
    exact heq.symm.trans hb2

end IsPGroup
