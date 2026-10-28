module
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic

/-!
# Lifting the seed vector through root displacement spaces

Write D(g) for the image of g-1. If t*x*t⁻¹ = z*x and z fixes D(x),
then D(z) lies in D(x) + t D(x). The seed vector and a lower-module
vector span the two-dimensional D(x). In the natural orientation, t
fixes that plane, so it equals D(z). In the dual orientation the first
bound has three generators. A second root r centralizes z, fixes the
seed vector, and moves the extra lower direction outside the bound.
Consequently that direction cannot occur in D(z), and dimension two
again gives the seed vector in D(z).

These are conditional linear-action lemmas. Realizing the indicated
roots and lower directions in the actual marked source module is a
separate obligation. In particular the desired central-root membership
and fixation of the whole central-root image are not assumptions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, 13.8.25, printed p.962 (PDF p.979).
-/

public section

open Representation
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

omit [FiniteDimensional (ZMod 2) U] in
private theorem span_pair_finrank_le (v w : U) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({v, w} : Set U)) ≤ 2 := by
  classical
  have h := finrank_span_finset_le_card (R := ZMod 2) ({v, w} : Finset U)
  rw [Set.finrank, Finset.coe_insert, Finset.coe_singleton] at h
  exact h.trans (by simpa using Finset.card_insert_le v ({w} : Finset U))

private theorem eq_span_pair_of_rank_two (C : Submodule (ZMod 2) U)
    (hC : Module.finrank (ZMod 2) C = 2) (v w : U)
    (hv : v ∈ C) (hw : w ∈ C) (hw0 : w ≠ 0)
    (hvw : v ∉ Submodule.span (ZMod 2) ({w} : Set U)) :
    C = Submodule.span (ZMod 2) ({v, w} : Set U) := by
  apply (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · exact Submodule.span_le.mpr (by simp only [Set.insert_subset_iff, Set.singleton_subset_iff]; exact ⟨hv, hw⟩)
  · rw [show ({v, w} : Set U) = {w} ∪ {v} by ext; simp,
      Submodule.span_union, Submodule.finrank_sup_span_singleton hvw,
      finrank_span_singleton hw0, hC]

private theorem mem_of_rank_two_le_pair (C : Submodule (ZMod 2) U)
    (hC : Module.finrank (ZMod 2) C = 2) (v w : U)
    (h : C ≤ Submodule.span (ZMod 2) ({v, w} : Set U)) : v ∈ C := by
  have he : C = Submodule.span (ZMod 2) ({v, w} : Set U) :=
    Submodule.eq_of_le_of_finrank_eq h (by
      have hle := Submodule.finrank_mono h
      have hge := span_pair_finrank_le v w
      omega)
  rw [he]
  exact Submodule.subset_span (by simp)

omit [FiniteDimensional (ZMod 2) U] in
private theorem displacement_conjugate (t x : H) (u : U) :
    ρ (t * x * t⁻¹) u - u = ρ t (ρ x (ρ t⁻¹ u) - ρ t⁻¹ u) := by
  rw [map_sub]
  simp only [map_mul, Module.End.mul_apply]
  have ht : ρ t (ρ t⁻¹ u) = u := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [ht]

omit [FiniteDimensional (ZMod 2) U] in
private theorem range_conjugate_bound (x z t : H)
    (hconj : t * x * t⁻¹ = z * x)
    (C : Submodule (ZMod 2) U)
    (hx : LinearMap.range (ρ x - 1) ≤ C)
    (htx : ∀ u ∈ LinearMap.range (ρ x - 1), ρ t u ∈ C)
    (hzx : ∀ u ∈ LinearMap.range (ρ x - 1), ρ z u = u) :
    LinearMap.range (ρ z - 1) ≤ C := by
  rintro _ ⟨u, rfl⟩
  have hu : ρ x u - u ∈ LinearMap.range (ρ x - 1) := ⟨u, rfl⟩
  have hu' : ρ x (ρ t⁻¹ u) - ρ t⁻¹ u ∈ LinearMap.range (ρ x - 1) := ⟨_, rfl⟩
  have hc := C.sub_mem (htx _ hu') (hx hu)
  rw [← displacement_conjugate ρ, hconj, map_mul, Module.End.mul_apply] at hc
  have hz := hzx _ hu
  rw [map_sub] at hz
  have he : ρ z (ρ x u) - u - (ρ x u - u) = ρ z u - u := by
    rw [sub_eq_iff_eq_add] at hz
    rw [hz]
    abel
  change ρ z u - u ∈ C
  exact he ▸ hc

/-- If a conjugating root fixes the lower displacement line, it transports the seed
fixed vector into the central-root displacement space. -/
theorem mem_range_of_fixed_lower_line (x z t : H)
    (hconj : t * x * t⁻¹ = z * x) (v w : U)
    (hx : Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) = 2)
    (hz : Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) = 2)
    (hv : v ∈ LinearMap.range (ρ x - 1)) (hw : w ∈ LinearMap.range (ρ x - 1))
    (hw0 : w ≠ 0) (hvw : v ∉ Submodule.span (ZMod 2) ({w} : Set U))
    (htv : ρ t v = v) (htw : ρ t w = w)
    (hzv : ρ z v = v) (hzw : ρ z w = w) :
    v ∈ LinearMap.range (ρ z - 1) := by
  have he := eq_span_pair_of_rank_two (LinearMap.range (ρ x - 1)) hx v w hv hw hw0 hvw
  apply mem_of_rank_two_le_pair (LinearMap.range (ρ z - 1)) hz v w
  apply range_conjugate_bound ρ x z t hconj _ he.le
  · intro u hu
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp (he ▸ hu)
    rw [map_add, map_smul, map_smul, htv, htw]
    exact Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩
  · intro u hu
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp (he ▸ hu)
    rw [map_add, map_smul, map_smul, hzv, hzw]

/-- In the dual orientation, a second shear excludes a lower-module error. The three
lower directions are separated before asserting membership in the central root image. -/
theorem mem_range_of_lower_shear (x z t r : H)
    (hconj : t * x * t⁻¹ = z * x) (hrz : r * z = z * r)
    (v w a b : U)
    (hx : Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) = 2)
    (hz : Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) = 2)
    (hv : v ∈ LinearMap.range (ρ x - 1)) (hw : w ∈ LinearMap.range (ρ x - 1))
    (hw0 : w ≠ 0) (hvw : v ∉ Submodule.span (ZMod 2) ({w} : Set U))
    (htv : ρ t v = v) (htw : ρ t w = w + a)
    (hzv : ρ z v = v) (hzw : ρ z w = w)
    (hrv : ρ r v = v) (hrw : ρ r w = w + b) (hra : ρ r a = a)
    (hb : b ∉ Submodule.span (ZMod 2) ({v, w, a} : Set U)) :
    v ∈ LinearMap.range (ρ z - 1) := by
  let C := LinearMap.range (ρ z - 1)
  let S := Submodule.span (ZMod 2) ({v, w, a} : Set U)
  have he := eq_span_pair_of_rank_two (LinearMap.range (ρ x - 1)) hx v w hv hw hw0 hvw
  have hxS : LinearMap.range (ρ x - 1) ≤ S := by
    rw [he]
    apply Submodule.span_mono
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
    tauto
  have hCS : C ≤ S := by
    apply range_conjugate_bound ρ x z t hconj S hxS
    · intro u hu
      obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp (he ▸ hu)
      rw [map_add, map_smul, map_smul, htv, htw, smul_add, ← add_assoc]
      exact Submodule.mem_span_triple.mpr ⟨c, d, d, rfl⟩
    · intro u hu
      obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp (he ▸ hu)
      rw [map_add, map_smul, map_smul, hzv, hzw]
  have hrC : ∀ u ∈ C, ρ r u ∈ C := by
    rintro _ ⟨u, rfl⟩
    refine ⟨ρ r u, ?_⟩
    change ρ z (ρ r u) - ρ r u = ρ r (ρ z u - u)
    rw [map_sub, ← Module.End.mul_apply, ← map_mul, ← hrz, map_mul,
      Module.End.mul_apply]
  apply mem_of_rank_two_le_pair C hz v a
  intro u hu
  obtain ⟨c, d, f, heq⟩ := Submodule.mem_span_triple.mp (hCS hu)
  have hdiff := S.sub_mem (hCS (hrC u hu)) (hCS hu)
  have heq' : ρ r u - u = d • b := by
    rw [← heq, map_add, map_add, map_smul, map_smul, map_smul, hrv, hrw, hra, smul_add]
    abel
  rw [heq'] at hdiff
  have hd : d = 0 := by
    rcases (by decide : ∀ d : ZMod 2, d = 0 ∨ d = 1) d with hd | hd
    · exact hd
    · exact False.elim (hb (by simpa [hd] using hdiff))
  exact Submodule.mem_span_pair.mpr ⟨c, f, by simpa [hd] using heq⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.CyclicMarking.RootSeed
