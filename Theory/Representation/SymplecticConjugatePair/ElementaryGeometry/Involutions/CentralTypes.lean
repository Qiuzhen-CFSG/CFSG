module

public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Center
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.Basic

/-!
# Suzuki types in the central root plane

Conjugation transports the actual moved space and preserves the symplectic
orthogonality test. For the central matrix with parameters `(s,t)`, the moved
space is the standard point when `s ≠ 0, t = 0`, and the standard plane when
`t ≠ 0`. Its pairing with a vector and its image is `s` times the square of
the first lower coordinate. Thus the two coordinate roots have Suzuki types
b₁ and a₂, and the mixed elements have type c₂.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Definition E.2.6, printed p.218, and H.7, printed pp.388–389.
-/

public section

open scoped Matrix
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes

namespace SymplecticConjugatePair.Involutions
set_option linter.unusedSimpArgs false
variable {F : Type*} [Field F]

lemma movedSpace_conj (h g : Sp F) :
    movedSpace (h*g*h⁻¹) = (movedSpace g).map (toLinear h).toLinearMap := by
  ext v
  constructor
  · rintro ⟨x,rfl⟩
    refine ⟨g • (h⁻¹ • x) - h⁻¹ • x, ⟨h⁻¹ • x,rfl⟩, ?_⟩
    change toLinear h (g • (h⁻¹ • x) - h⁻¹ • x) = (h*g*h⁻¹) • x - x
    simp only [map_sub,toLinear_apply,mul_smul,smul_inv_smul]
  · rintro ⟨_,⟨x,rfl⟩,rfl⟩
    refine ⟨h • x, ?_⟩
    change (h*g*h⁻¹) • (h • x) - h • x = toLinear h (g • x-x)
    simp only [map_sub,toLinear_apply,mul_smul,inv_smul_smul]

lemma moved_finrank_conj (h g : Sp F) :
    Module.finrank F (movedSpace (h*g*h⁻¹)) = Module.finrank F (movedSpace g) := by
  rw [movedSpace_conj,LinearEquiv.finrank_map_eq]

lemma orthogonal_conj_iff (h g : Sp F) :
    (∀ v : Vector F, form F v ((h*g*h⁻¹) • v) = 0) ↔
      ∀ v : Vector F, form F v (g • v) = 0 := by
  have he (v : Vector F) : form F (h • v) ((h*g*h⁻¹) • (h • v)) =
      form F v (g • v) := by
    simp only [mul_smul,inv_smul_smul,preserves_form]
  constructor
  · intro ha v
    rw [← he]
    exact ha _
  · intro ha v
    obtain ⟨w,rfl⟩ := (toLinear h).surjective v
    exact (he w).trans (ha w)

lemma isB1_conj_iff (h g : Sp F) : IsB1 (h*g*h⁻¹) ↔ IsB1 g := by
  unfold IsB1
  rw [moved_finrank_conj,show orderOf (h*g*h⁻¹) = orderOf g from (MulAut.conj h).orderOf_eq g]

lemma isA2_conj_iff (h g : Sp F) : IsA2 (h*g*h⁻¹) ↔ IsA2 g := by
  unfold IsA2
  rw [moved_finrank_conj,orthogonal_conj_iff,
    show orderOf (h*g*h⁻¹) = orderOf g from (MulAut.conj h).orderOf_eq g]

lemma isC2_conj_iff (h g : Sp F) : IsC2 (h*g*h⁻¹) ↔ IsC2 g := by
  classical
  have he := orthogonal_conj_iff h g
  have he' : (∃ v : Vector F, form F v ((h*g*h⁻¹) • v) ≠ 0) ↔
      ∃ v : Vector F, form F v (g • v) ≠ 0 := by
    simpa only [not_forall] using not_congr he
  unfold IsC2
  rw [moved_finrank_conj,he',
    show orderOf (h*g*h⁻¹) = orderOf g from (MulAut.conj h).orderOf_eq g]

variable [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
lemma central_moved_apply (s t : F) (v : Vector F) :
    (rootElement 0 s * rootElement 4 t) • v - v =
      Sum.elim ![s*v (.inr 0)+t*v (.inr 1), t*v (.inr 0)] ![0,0] := by
  rw [Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,central_matrix]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,fromBlocks,one_apply]

lemma central_movedSpace_of_right_ne_zero (s : F) {t : F} (ht : t ≠ 0) :
    movedSpace (rootElement 0 s * rootElement 4 t) = plane F := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩ i
    change ((rootElement 0 s * rootElement 4 t) • w - w) (.inr i) = 0
    rw [central_moved_apply]
    fin_cases i <;> rfl
  · intro hv
    refine ⟨Sum.elim ![0,0] ![v (.inl 1)/t, (v (.inl 0)-s*(v (.inl 1)/t))/t], ?_⟩
    change (rootElement 0 s * rootElement 4 t) • _ - _ = v
    simp only [LinearMap.id_apply]
    rw [central_moved_apply]
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [hv 0,hv 1]
    all_goals field_simp
    all_goals ring

lemma central_movedSpace_of_right_zero {s : F} (hs : s ≠ 0) :
    movedSpace (rootElement 0 s * rootElement 4 0) = point F := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    change (rootElement 0 s * rootElement 4 0) • w - w ∈ point F
    rw [central_moved_apply,mem_point_iff]
    simp
  · intro hv
    obtain ⟨hv1,hv2⟩ := (mem_point_iff _).mp hv
    refine ⟨Sum.elim ![0,0] ![v (.inl 0)/s,0],?_⟩
    change (rootElement 0 s * rootElement 4 0) • _ - _ = v
    simp only [LinearMap.id_apply]
    rw [central_moved_apply]
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [hv1,hv2 0,hv2 1]
    all_goals field_simp

lemma central_form (s t : F) (v : Vector F) :
    form F v ((rootElement 0 s * rootElement 4 t) • v) = s*(v (.inr 0))^2 := by
  rw [form_apply,Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,central_matrix]
  simp only [Fin.sum_univ_two,mulVec,dotProduct,Fintype.sum_sum_type,fromBlocks,
    one_apply,Fin.isValue, ↓reduceIte,mul_one,mul_zero,zero_mul,add_zero,zero_add]
  ring_nf
  simp [CharTwo.neg_eq,CharTwo.two_eq_zero]

lemma central_orderOf {s t : F} (h : s ≠ 0 ∨ t ≠ 0) :
    orderOf (rootElement 0 s * rootElement 4 t) = 2 := by
  apply orderOf_eq_prime
  · have he := CentralRootGeometry.theta_add s t s t
    rw [CharTwo.add_self_eq_zero,CharTwo.add_self_eq_zero,
      show CentralRootGeometry.theta (0:F) 0 = 1 from CentralRootGeometry.element_zero] at he
    simpa only [Subgroup.coe_mul,Subgroup.coe_one,CentralRootGeometry.theta_val,pow_two]
      using congrArg Subtype.val he
  · intro he
    have hm := congrArg Subtype.val he
    rw [central_matrix] at hm
    have hs := congrArg (fun M => M (.inl 0) (.inr 0)) hm
    have ht := congrArg (fun M => M (.inl 0) (.inr 1)) hm
    exact h.elim (fun h => h (by simpa using hs)) (fun h => h (by simpa using ht))

lemma central_isB1 {s : F} (hs : s ≠ 0) : IsB1 (rootElement 0 s * rootElement 4 0) := by
  refine ⟨central_orderOf (Or.inl hs),?_⟩
  rw [central_movedSpace_of_right_zero hs,finrank_point]

lemma central_isA2 {t : F} (ht : t ≠ 0) : IsA2 (rootElement 0 0 * rootElement 4 t) := by
  refine ⟨central_orderOf (Or.inr ht),?_,?_⟩
  · rw [central_movedSpace_of_right_ne_zero 0 ht,finrank_plane]
  · intro v
    simp only [central_form,zero_mul]

lemma central_isC2 {s t : F} (hs : s ≠ 0) (ht : t ≠ 0) :
    IsC2 (rootElement 0 s * rootElement 4 t) := by
  refine ⟨central_orderOf (Or.inl hs),?_,?_⟩
  · rw [central_movedSpace_of_right_ne_zero s ht,finrank_plane]
  · refine ⟨Pi.single (.inr 0) 1,?_⟩
    simpa only [central_form,Pi.single_eq_same,one_pow,mul_one] using hs



lemma central_isB1_iff (s t : F) : IsB1 (rootElement 0 s * rootElement 4 t) ↔ s ≠ 0 ∧ t = 0 := by
  constructor
  · intro h
    have ht : t = 0 := by
      by_contra ht
      have hm := h.2
      rw [central_movedSpace_of_right_ne_zero s ht,finrank_plane] at hm
      omega
    refine ⟨?_,ht⟩
    intro hs
    have ho := h.1
    simp [hs,ht,RootSubgroup.element_zero] at ho
  · rintro ⟨hs,rfl⟩
    exact central_isB1 hs

lemma central_isA2_iff (s t : F) : IsA2 (rootElement 0 s * rootElement 4 t) ↔ s = 0 ∧ t ≠ 0 := by
  constructor
  · intro h
    have hs : s = 0 := by
      have he := h.2.2 (Pi.single (.inr 0) 1)
      simpa only [central_form,Pi.single_eq_same,one_pow,mul_one] using he
    refine ⟨hs,?_⟩
    intro ht
    have ho := h.1
    simp [hs,ht,RootSubgroup.element_zero] at ho
  · rintro ⟨rfl,ht⟩
    exact central_isA2 ht

lemma central_isC2_iff (s t : F) : IsC2 (rootElement 0 s * rootElement 4 t) ↔ s ≠ 0 ∧ t ≠ 0 := by
  constructor
  · rintro ⟨ho,hm,v,hv⟩
    have hs : s ≠ 0 := by
      intro hs
      simp only [central_form,hs,zero_mul,ne_eq,not_true_eq_false] at hv
    refine ⟨hs,?_⟩
    intro ht
    rw [ht,central_movedSpace_of_right_zero hs,finrank_point] at hm
    omega
  · rintro ⟨hs,ht⟩
    exact central_isC2 hs ht
end SymplecticConjugatePair.Involutions
