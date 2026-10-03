module

public import Theory.GroupTheory.PGroup.Omega
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.Group

/-!
# Transporting an elementary eight from an index-two subgroup

An automorphism-selection theorem for a finite model can be transported to an
arbitrary index-two extension. Conjugation by an outside element has inner
square. If the model has more than two central elements of square one, a
central omega subgroup of order two forces this conjugation to move one of
those elements. A normal elementary eight invariant under this conjugation
is normal in the whole extension.

This isolates the intrinsic extension step used for the order-64 specialization
of Janko–Thompson, Math. Z. 113 (1970), §§1.3–1.4, printed p.386.
-/

namespace Subgroup

private theorem center_of_index_two_fixed {P : Type*} [Group P]
    (C : Subgroup P) (hi : C.index = 2) (t : P) (ht : t ∉ C)
    (z : P) (hc : ∀ c ∈ C, c * z = z * c) (hf : t * z * t⁻¹ = z) :
    z ∈ center P := by
  apply mem_center_iff.mpr
  intro g
  by_cases hg : g ∈ C
  · exact hc g hg
  · have ha : g * t⁻¹ ∈ C := (C.mul_mem_iff_of_index_two hi).mpr (by
      simp only [hg, C.inv_mem_iff, ht])
    have hconj : g * z * g⁻¹ = z := by
      calc
        g * z * g⁻¹ = (g * t⁻¹) * (t * z * t⁻¹) * (g * t⁻¹)⁻¹ := by group
        _ = (g * t⁻¹) * z * (g * t⁻¹)⁻¹ := by rw [hf]
        _ = z := by rw [hc _ ha, mul_inv_cancel_right]
    exact (mul_inv_eq_iff_eq_mul).mp hconj

/-- An invariant-eight selection theorem for a model gives normal eights in
index-two extensions whose central omega subgroup has order two. -/
public theorem exists_normal_elementary_eight_of_index_two_selection
    {P K : Type*} [Group P] [Finite P] [Group K] [Finite K]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (C : Subgroup P) (hi : C.index = 2) (e : C ≃* K)
    (hK : 2 < Nat.card {z : K // z ∈ center K ∧ z ^ 2 = 1})
    (hselect : ∀ f : MulAut K,
      (∃ c : K, ∀ x : K, f (f x) = c * x * c⁻¹) →
      (¬ ∀ z : K, z ∈ center K → z ^ 2 = 1 → f z = z) →
      ∃ U : Subgroup K, U.Normal ∧ IsElementaryAbelian 2 U ∧
        8 ≤ Nat.card U ∧ ∀ u ∈ U, f u ∈ U) :
    ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  classical
  let : C.Normal := normal_of_index_eq_two hi
  have hproper : C ≠ ⊤ := by
    intro h
    simp [h] at hi
  obtain ⟨t, ht⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hproper)
  simp only [mem_top, true_and] at ht
  let a : MulAut C := MulAut.conjNormal t
  let f : MulAut K := (MulAut.congr e) a
  have hf (x : K) : f x = e (a (e.symm x)) := rfl
  have hsquare : ∃ c : K, ∀ x : K, f (f x) = c * x * c⁻¹ := by
    have ht2 : t ^ 2 ∈ C := sq_mem_of_index_two hi t
    refine ⟨e ⟨t ^ 2, ht2⟩, fun x => ?_⟩
    apply e.symm.injective
    simp only [hf, map_mul, map_inv, e.symm_apply_apply]
    apply Subtype.ext
    change t * (t * (e.symm x : P) * t⁻¹) * t⁻¹ =
      t ^ 2 * (e.symm x : P) * (t ^ 2)⁻¹
    simp only [pow_two]
    group
  have hmove : ¬ ∀ z : K, z ∈ center K → z ^ 2 = 1 → f z = z := by
    intro hfix
    have hcentral (z : K) (hz : z ∈ center K) (hz2 : z ^ 2 = 1) :
        (e.symm z : P) ∈ center P := by
      apply center_of_index_two_fixed C hi t ht
      · intro c hc
        have hh : (⟨c, hc⟩ : C) * e.symm z = e.symm z * ⟨c, hc⟩ := by
          apply e.injective
          simpa only [map_mul, e.apply_symm_apply] using (mem_center_iff.mp hz (e ⟨c, hc⟩))
        exact congrArg Subtype.val hh
      · have hh : a (e.symm z) = e.symm z := e.injective (by
          rw [← hf, hfix z hz hz2, e.apply_symm_apply])
        exact congrArg Subtype.val hh
    let j : {z : K // z ∈ center K ∧ z ^ 2 = 1} → omega₁ (center P) (p := 2) :=
      fun z => ⟨⟨e.symm z.val, hcentral z.val z.property.1 z.property.2⟩, by
        apply subset_closure
        change (⟨(e.symm z.val : P), hcentral z.val z.property.1 z.property.2⟩ : center P) ^
          (2 ^ 1) = 1
        apply Subtype.ext
        have hh : (e.symm z.val) ^ 2 = 1 := by rw [← map_pow, z.property.2, map_one]
        simpa using congrArg Subtype.val hh⟩
    have hj : Function.Injective j := by
      intro x y h
      apply Subtype.ext
      apply e.symm.injective
      apply Subtype.ext
      exact congrArg (fun v : omega₁ (center P) (p := 2) => (v.val : P)) h
    have hbound := Nat.card_le_card_of_injective j hj
    omega
  obtain ⟨U, hUn, hUe, hUc, hUa⟩ := hselect f hsquare hmove
  let D : Subgroup C := U.map e.symm.toMonoidHom
  let E : Subgroup P := D.map C.subtype
  let : U.Normal := hUn
  let : IsElementaryAbelian 2 U := hUe
  let : D.Normal := hUn.map e.symm.toMonoidHom e.symm.surjective
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map e.symm.toMonoidHom
  have hDa : ∀ d ∈ D, a d ∈ D := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨f u, hUa u hu, ?_⟩
    exact e.symm_apply_apply (a (e.symm u))
  have hEn : E.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨d, hd, rfl⟩ g
    by_cases hg : g ∈ C
    · exact ⟨(⟨g, hg⟩ : C) * d * (⟨g, hg⟩ : C)⁻¹,
        (inferInstance : D.Normal).conj_mem d hd ⟨g, hg⟩, rfl⟩
    · have hgt : g * t⁻¹ ∈ C := (C.mul_mem_iff_of_index_two hi).mpr (by
        simp only [hg, C.inv_mem_iff, ht])
      refine ⟨(⟨g * t⁻¹, hgt⟩ : C) * a d * (⟨g * t⁻¹, hgt⟩ : C)⁻¹,
        (inferInstance : D.Normal).conj_mem (a d) (hDa d hd) ⟨g * t⁻¹, hgt⟩, ?_⟩
      change (g * t⁻¹) * (t * (d : P) * t⁻¹) * (g * t⁻¹)⁻¹ = g * (d : P) * g⁻¹
      group
  refine ⟨E, hEn, IsElementaryAbelian.map C.subtype, ?_⟩
  simpa only [E, D, card_map_of_injective C.subtype_injective,
    card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective] using hUc

end Subgroup
