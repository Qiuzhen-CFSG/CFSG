module

public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

/-!
# Centers of transposition transvections

In a faithful binary representation, if one transposition has displacement
rank one, all transpositions do. Their unique nonzero displacement vectors
form an equivariant family. Equal centers force two transpositions to commute,
so centers of adjacent transpositions are distinct. Conjugating adjacent
transpositions then proves the triangle relation between their centers.

This supplies the geometric input for the augmentation-core map used in
Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.25, printed p.960
(PDF p.977), with the permutation core defined in B.3.1, printed p.83.
-/

public section

namespace BinaryPermutation.TransvectionCoreMap
open Equiv Representation.BinaryOffender
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

private theorem unique_nonzero_of_rank_one (d : E →ₗ[ZMod 2] E)
    (hd : Module.finrank (ZMod 2) d.range = 1) :
    ∃ c : E, c ≠ 0 ∧ c ∈ d.range ∧ ∀ v ∈ d.range, v = 0 ∨ v = c := by
  obtain ⟨c, hc, hspan⟩ := finrank_eq_one_iff'.mp hd
  refine ⟨c, fun h => hc (Subtype.ext h), c.property, ?_⟩
  intro v hv
  obtain ⟨r, hr⟩ := hspan ⟨v, hv⟩
  rcases (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) r with rfl | rfl
  · left; exact (congrArg Subtype.val hr).symm.trans (zero_smul _ _)
  · right; exact (congrArg Subtype.val hr).symm.trans (one_smul _ _)

/-- The displacement rank of one element is the codimension of its fixed space. -/
theorem rank_displacement_eq_fixedCodim {G : Type*} [Group G]
    [FiniteDimensional (ZMod 2) E] (ρ : Representation (ZMod 2) G E) (a : G) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) =
      fixedCodim ρ (Subgroup.zpowers a) := by
  have hk : (ρ a - LinearMap.id).ker = fixedSpace ρ (Subgroup.zpowers a) := by
    ext v
    rw [Subgroup.zpowers_eq_closure, mem_fixedSpace_closure_iff]
    simp [LinearMap.mem_ker, sub_eq_zero]
  have hr := (ρ a - LinearMap.id).finrank_range_add_finrank_ker
  rw [hk] at hr
  have hf := fixedCodim_add_finrank ρ (Subgroup.zpowers a)
  omega

variable {Ω : Type*} [DecidableEq Ω]
variable (ρ : Representation (ZMod 2) (Perm Ω) E)

/-- Conjugate transpositions have the same displacement rank. -/
theorem swap_rank_one [FiniteDimensional (ZMod 2) E]
    {a : Perm Ω} (ha : a.IsSwap)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (i j : Ω) (hij : i ≠ j) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ (swap i j) - LinearMap.id)) = 1 := by
  obtain ⟨x, y, hxy, rfl⟩ := ha
  obtain ⟨g, hg⟩ := isConj_iff.mp (Perm.isConj_swap hxy hij)
  have he : (Subgroup.zpowers (swap x y)).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (swap i j) := by
    rw [MonoidHom.map_zpowers]
    congr 1
  rw [rank_displacement_eq_fixedCodim] at hr ⊢
  rw [← he, fixedCodim_map_conj]
  exact hr

variable (hr : ∀ i j : Ω, i ≠ j →
  Module.finrank (ZMod 2) (LinearMap.range (ρ (swap i j) - LinearMap.id)) = 1)

/-- The unique nonzero displacement of a transposition, extended by zero on the diagonal. -/
noncomputable def center (i j : Ω) : E :=
  if h : i = j then 0 else
    (unique_nonzero_of_rank_one (ρ (swap i j) - LinearMap.id) (hr i j h)).choose

@[simp] theorem center_self (i : Ω) : center ρ hr i i = 0 := by simp [center]

theorem center_spec (i j : Ω) (hij : i ≠ j) :
    center ρ hr i j ≠ 0 ∧
    center ρ hr i j ∈ LinearMap.range (ρ (swap i j) - LinearMap.id) ∧
    ∀ v ∈ LinearMap.range (ρ (swap i j) - LinearMap.id), v = 0 ∨ v = center ρ hr i j := by
  simpa only [center, dif_neg hij] using
    (unique_nonzero_of_rank_one (ρ (swap i j) - LinearMap.id) (hr i j hij)).choose_spec

theorem center_mem (i j : Ω) :
    center ρ hr i j ∈ LinearMap.range (ρ (swap i j) - LinearMap.id) := by
  by_cases hij : i = j
  · subst j; simp
  · exact (center_spec ρ hr i j hij).2.1

theorem displacement_cases (i j : Ω) (v : E) :
    ρ (swap i j) v - v = 0 ∨ ρ (swap i j) v - v = center ρ hr i j := by
  by_cases hij : i = j
  · subst j; left; simp only [swap_self]; change ρ 1 v - v = 0; simp
  · exact (center_spec ρ hr i j hij).2.2 _ ⟨v, rfl⟩

theorem center_symm (i j : Ω) : center ρ hr i j = center ρ hr j i := by
  by_cases hij : i = j
  · subst j; rfl
  exact ((center_spec ρ hr j i (Ne.symm hij)).2.2 _
    (by simpa only [swap_comm] using center_mem ρ hr i j)).resolve_left
      (center_spec ρ hr i j hij).1

omit [DecidableEq Ω] in
private theorem action_injective (g : Perm Ω) : Function.Injective (ρ g) := by
  intro x y h
  have hh := congrArg (ρ g⁻¹) h
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] using hh

/-- The centers form an equivariant family indexed by pairs of letters. -/
theorem center_equivariant (g : Perm Ω) (i j : Ω) :
    ρ g (center ρ hr i j) = center ρ hr (g i) (g j) := by
  by_cases hij : i = j
  · subst j; simp
  have hgi : g i ≠ g j := fun h => hij (g.injective h)
  apply ((center_spec ρ hr (g i) (g j) hgi).2.2 _ ?_).resolve_left
  · exact fun h => (center_spec ρ hr i j hij).1
      (action_injective ρ g (h.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ := center_mem ρ hr i j
  refine ⟨ρ g v, ?_⟩
  change ρ (swap (g i) (g j)) (ρ g v) - ρ g v = _
  rw [swap_apply_apply]
  simp only [map_mul, Module.End.mul_apply]
  have hc : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hc, ← map_sub]
  exact congrArg (ρ g) hv

/-- Every transposition fixes its own center. -/
theorem center_fixed (i j : Ω) : ρ (swap i j) (center ρ hr i j) = center ρ hr i j := by
  rw [center_equivariant, swap_apply_left, swap_apply_right, center_symm]

private theorem commute_of_same_center (hρ : Function.Injective ρ)
    {i j k l : Ω} (hc : center ρ hr i j = center ρ hr k l) :
    Commute (swap i j) (swap k l) := by
  apply hρ
  rw [map_mul, map_mul]
  ext v
  have ht := displacement_cases ρ hr i j v
  have hs := displacement_cases ρ hr k l v
  have htc : ρ (swap i j) (center ρ hr k l) = center ρ hr k l := by
    rw [← hc]; exact center_fixed ρ hr i j
  have hsc : ρ (swap k l) (center ρ hr i j) = center ρ hr i j := by
    rw [hc]; exact center_fixed ρ hr k l
  rcases ht with ht | ht <;> rcases hs with hs | hs
  · simp only [Module.End.mul_apply, sub_eq_zero.mp ht, sub_eq_zero.mp hs]
  · rw [sub_eq_zero] at ht
    have hs' := sub_eq_iff_eq_add.mp hs
    simp only [Module.End.mul_apply, hs', map_add, htc, ht]
  · rw [sub_eq_zero] at hs
    have ht' := sub_eq_iff_eq_add.mp ht
    simp only [Module.End.mul_apply, ht', map_add, hsc, hs]
  · have ht' := sub_eq_iff_eq_add.mp ht
    have hs' := sub_eq_iff_eq_add.mp hs
    simp only [Module.End.mul_apply, ht', hs', map_add, htc, hsc]
    abel

private theorem adjacent_not_commute {i j k : Ω} (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) : ¬ Commute (swap i j) (swap j k) := by
  intro h
  have hh := congrArg (fun g : Perm Ω => g i) h.eq
  simp [Perm.mul_apply, swap_apply_of_ne_of_ne hij hik, hjk] at hh

/-- Adjacent transpositions have distinct centers in a faithful action. -/
theorem center_adjacent_ne (hρ : Function.Injective ρ) {i j k : Ω}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    center ρ hr i j ≠ center ρ hr j k := by
  intro h
  exact adjacent_not_commute hij hjk hik (commute_of_same_center ρ hr hρ h)

/-- The triangle relation makes the center family descend to the augmentation core. -/
theorem center_triangle (hρ : Function.Injective ρ) (i j k : Ω) :
    center ρ hr i j + center ρ hr j k = center ρ hr i k := by
  by_cases hij : i = j
  · subst j; simp
  by_cases hjk : j = k
  · subst k; simp
  by_cases hik : i = k
  · subst k; rw [center_symm ρ hr j i]; simp [ZModModule.add_self]
  have he : ρ (swap j k) (center ρ hr i j) = center ρ hr i k := by
    rw [center_equivariant, swap_apply_of_ne_of_ne hij hik, swap_apply_left]
  have hn : center ρ hr i k ≠ center ρ hr i j := by
    rw [center_symm ρ hr i k]
    exact center_adjacent_ne ρ hr hρ (Ne.symm hik) hij (Ne.symm hjk)
  rcases displacement_cases ρ hr j k (center ρ hr i j) with hz | hc
  · exact (hn (he.symm.trans (sub_eq_zero.mp hz))).elim
  · rw [he] at hc
    exact (add_comm _ _).trans (sub_eq_iff_eq_add.mp hc).symm

end BinaryPermutation.TransvectionCoreMap
