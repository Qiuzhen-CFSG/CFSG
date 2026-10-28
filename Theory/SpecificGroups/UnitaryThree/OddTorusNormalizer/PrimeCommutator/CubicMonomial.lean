module
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.NormalizerAction

/-!
# Cubes outside the diagonal unitary frame torus

An odd-order element outside the diagonal torus acts as a three-cycle on
its three frame lines. In monomial coordinates its cube is the product of
its three nonzero entries, which is its determinant and hence one.
The actual scalar quotient satisfies the same conclusion by lifting the
frame permutation. In particular, both literal order-nine source witnesses
from Proposition 16.5 lie in the same frame torus.

Source: GLS IV, Chapter 4, Lemma 3.11(b); the order-nine branch repairs the
terminal unitary calculation in Chapter 2, Proposition 16.5.
-/

noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E]
private theorem perm_three_cycle (σ : Equiv.Perm (Fin 3)) (h3 : σ ^ 3 = 1) (hne : σ ≠ 1) :
    (σ 0 = 1 ∧ σ 1 = 2 ∧ σ 2 = 0) ∨ (σ 0 = 2 ∧ σ 1 = 0 ∧ σ 2 = 1) := by
  have h : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 →
      (σ 0 = 1 ∧ σ 1 = 2 ∧ σ 2 = 0) ∨ (σ 0 = 2 ∧ σ 1 = 0 ∧ σ 2 = 1) := by
    decide +kernel
  exact h σ h3 hne

private theorem coordinate_cube_of_cycle (x : coordinateStabilizer (E := E))
    (hd : Matrix.det x.val.val = 1)
    (h3 : coordinateAction x ^ 3 = 1) (hne : coordinateAction x ≠ 1) : x ^ 3 = 1 := by
  have hz (i j : Fin 3) (h : i ≠ coordinateAction x j) : x.val.val i j = 0 :=
    (coordinateIndex_spec x j).2 i h
  rcases perm_three_cycle (coordinateAction x) h3 hne with ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩
  all_goals
    have hz00 := hz 0 0 (by simp [h0])
    have hz11 := hz 1 1 (by simp [h1])
    have hz22 := hz 2 2 (by simp [h2])
    apply Subtype.ext
    apply Units.ext
    change x.val.val ^ 3 = 1
  · have hz01 := hz 0 1 (by simp [h1])
    have hz12 := hz 1 2 (by simp [h2])
    have hz20 := hz 2 0 (by simp [h0])
    simp only [Matrix.det_fin_three, hz00,hz11,hz22,hz01,hz12,hz20,
      zero_mul,mul_zero,zero_add,add_zero,sub_zero] at hd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, hz00,hz11,hz22,hz01,hz12,hz20] <;>
      linear_combination hd
  · have hz02 := hz 0 2 (by simp [h2])
    have hz10 := hz 1 0 (by simp [h0])
    have hz21 := hz 2 1 (by simp [h1])
    simp only [Matrix.det_fin_three, hz00,hz11,hz22,hz02,hz10,hz21,
      zero_mul,mul_zero,zero_add,add_zero,sub_zero] at hd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, hz00,hz11,hz22,hz02,hz10,hz21] <;>
      linear_combination hd


private theorem perm_cube_of_odd_order (σ : Equiv.Perm (Fin 3))
    (hodd : Odd (orderOf σ)) : σ ^ 3 = 1 := by
  have h6 : orderOf σ ∣ 6 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using
      orderOf_dvd_natCard σ
  have hcop : Nat.Coprime (orderOf σ) 2 := Nat.coprime_two_right.mpr hodd
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_mul_left.mp h6)

private theorem special_monomial_cube_of_action_cube
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (g : specialFrameMonomial J P)
    (h3 : specialMonomialAction J P g ^ 3 = 1)
    (hne : specialMonomialAction J P g ≠ 1) : g ^ 3 = 1 := by
  let x := specialMonomialCoordinates J P g
  have hd : Matrix.det x.val.val = 1 := by
    have hdu : GeneralLinearGroup.det x.val = 1 := by
      change GeneralLinearGroup.det (P.val⁻¹ * g.val.val * P.val) = 1
      rw [map_mul,map_mul,map_inv,(HermitianForm.mem_specialSubgroup_iff J _).mp g.val.property |>.2]
      simp
    exact congrArg Units.val hdu
  have hx := coordinate_cube_of_cycle x hd h3 hne
  have hi : Function.Injective (specialMonomialCoordinates J P) := by
    intro a b hab
    apply Subtype.ext
    apply (MulAut.conj P.val⁻¹).injective.comp J.specialSubgroup.subtype_injective
    exact congrArg Subtype.val hab
  apply hi
  simpa only [map_pow,map_one] using hx

variable [Finite E]
public theorem specialFrameNormalizer_cube_of_odd_not_mem
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hq : 2 ≤ q) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (g : J.specialSubgroup) (hg : g ∈ normalizer (specialFrameTorus J P))
    (hodd : Odd (orderOf g)) (hout : g ∉ specialFrameTorus J P) : g ^ 3 = 1 := by
  let gm : specialFrameMonomial J P :=
    ⟨g,(specialFrameTorus_normalizer_eq_monomial J P q hq hcard hfixed) ▸ hg⟩
  have hne : specialMonomialAction J P gm ≠ 1 := by
    intro hh
    have hm : gm ∈ (specialMonomialAction J P).ker := hh
    rw [specialMonomialAction_ker] at hm
    exact hout hm
  have h3 : specialMonomialAction J P gm ^ 3 = 1 :=
    perm_cube_of_odd_order _ (hodd.of_dvd_nat (by
      simpa only [gm, Subgroup.orderOf_mk] using orderOf_map_dvd (specialMonomialAction J P) gm))
  exact congrArg Subtype.val (special_monomial_cube_of_action_cube J P gm h3 hne)

public theorem projectiveFrameNormalizer_cube_of_odd_not_mem
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hq : 2 ≤ q) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (hg : g ∈ normalizer (projectiveFrameTorus J P))
    (hodd : Odd (orderOf g)) (hout : g ∉ projectiveFrameTorus J P) : g ^ 3 = 1 := by
  let gn : normalizer (projectiveFrameTorus J P) := ⟨g,hg⟩
  let a := projectiveNormalizerAction J P q hq hcard hfixed
  have hne : a gn ≠ 1 := by
    intro hh
    have hm : gn ∈ a.ker := hh
    rw [show a.ker = _ from projectiveNormalizerAction_ker J P q hq hcard hfixed] at hm
    exact hout hm
  have h3 : a gn ^ 3 = 1 := perm_cube_of_odd_order _
    (hodd.of_dvd_nat (by simpa only [gn, Subgroup.orderOf_mk] using orderOf_map_dvd a gn))
  obtain ⟨x,hx⟩ := frameNormalizerProjection_surjective J P gn
  have he : specialNormalizerAction J P q hq hcard hfixed x = a gn := by
    rw [← projectiveNormalizerAction_projection, hx]
  let xm : specialFrameMonomial J P :=
    MulEquiv.subgroupCongr (specialFrameTorus_normalizer_eq_monomial J P q hq hcard hfixed) x
  have hxm : xm ^ 3 = 1 := special_monomial_cube_of_action_cube J P xm
    (he.trans (by rfl) ▸ h3) (fun hh => hne (he.symm.trans hh))
  have hx3 : x.val ^ 3 = 1 := congrArg Subtype.val hxm
  have hxg : J.specialToProjective x.val = g := congrArg Subtype.val hx
  rw [← hxg, ← map_pow, hx3, map_one]

/-- An element of order nine in the actual special frame normalizer is diagonal. -/
public theorem specialFrameNormalizer_mem_of_order_nine
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hq : 2 ≤ q) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (g : J.specialSubgroup) (hg : g ∈ normalizer (specialFrameTorus J P))
    (horder : orderOf g = 9) : g ∈ specialFrameTorus J P := by
  by_contra hout
  have hc := specialFrameNormalizer_cube_of_odd_not_mem J P q hq hcard hfixed g hg
    (horder ▸ (by decide : Odd 9)) hout
  have hd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hc
  norm_num [horder] at hd

/-- The same order-nine test holds after the literal scalar quotient. -/
public theorem projectiveFrameNormalizer_mem_of_order_nine
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hq : 2 ≤ q) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (hg : g ∈ normalizer (projectiveFrameTorus J P))
    (horder : orderOf g = 9) : g ∈ projectiveFrameTorus J P := by
  by_contra hout
  have hc := projectiveFrameNormalizer_cube_of_odd_not_mem J P q hq hcard hfixed g hg
    (horder ▸ (by decide : Odd 9)) hout
  have hd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hc
  norm_num [horder] at hd
end UnitaryThree.OddTorusNormalizer

