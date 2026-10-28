module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Data.Set.Card

/-!
# Normalizers preserve short-orbit kernels

Conjugation by a normalizing element transports subgroup orbits bijectively.
It therefore preserves the points on two-point orbits and the intersection of
the subgroup with their pointwise fixer. A two-point orbit on which an element
moves a point consists exactly of that point and its image; this gives the
finite generator criterion used by the Held certificates.

This is the elementary action argument underlying the rank-four calculations
for the concrete subgroups associated with GLS3 Table 5.3p.
-/

public section
namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankFourKernel
open Subgroup MulAction

@[expose] public def shortPoints (H : Subgroup He) : Set (Fin 2058) :=
  {x | Nat.card (orbit H x) = 2}

private theorem card_orbit_normalizer (H : Subgroup He) {g : He}
    (hg : g ∈ normalizer (H : Set He)) (x : Fin 2058) :
    Nat.card (orbit H (g • x)) = Nat.card (orbit H x) := by
  have him : (fun y : Fin 2058 => g • y) '' orbit H x = orbit H (g • x) := by
    ext y
    constructor
    · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
      refine ⟨⟨g * h * g⁻¹, (mem_normalizer_iff.mp hg h).mp h.property⟩, ?_⟩
      change (g * (h : He) * g⁻¹) • (g • x) = g • ((h : He) • x)
      simp only [mul_smul, inv_smul_smul]
    · rintro ⟨h, rfl⟩
      refine ⟨(g⁻¹ * (h : He) * g) • x, ?_, ?_⟩
      · refine ⟨⟨g⁻¹ * h * g, ?_⟩, rfl⟩
        simpa only [inv_inv] using
          (mem_normalizer_iff.mp ((normalizer (H : Set He)).inv_mem hg) h).mp h.property
      · change g • ((g⁻¹ * (h : He) * g) • x) = (h : He) • (g • x)
        simp only [mul_smul, smul_inv_smul]
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, ← him]
  exact Set.ncard_image_of_injective _ (MulAction.injective g)

public theorem normalizer_preserves_short_kernel (H : Subgroup He) :
    normalizer (H : Set He) ≤
      normalizer ((H ⊓ fixingSubgroup He (shortPoints H) : Subgroup He) : Set He) := by
  apply le_normalizer_iff.mpr
  intro g hg z hz
  refine ⟨(mem_normalizer_iff.mp hg z).mp hz.1, ?_⟩
  apply (mem_fixingSubgroup_iff He).mpr
  intro x hx
  have hx' : g⁻¹ • x ∈ shortPoints H :=
    (card_orbit_normalizer H ((normalizer (H : Set He)).inv_mem hg) x).trans hx
  have hfix := (mem_fixingSubgroup_iff He).mp hz.2 (g⁻¹ • x) hx'
  simp only [mul_smul, hfix, smul_inv_smul]

private theorem pair_orbit (H : Subgroup He) (x : Fin 2058)
    (hx : x ∈ shortPoints H) (z : H) (hz : (z : He) • x ≠ x) :
    orbit H x = {x, (z : He) • x} := by
  obtain ⟨a, b, hab, heq⟩ := Set.ncard_eq_two.mp hx
  have hxmem : x = a ∨ x = b := by simpa only [heq, Set.mem_insert_iff,
    Set.mem_singleton_iff] using mem_orbit_self (M := H) x
  have hzmem : (z : He) • x = a ∨ (z : He) • x = b := by
    have hm : (z : He) • x ∈ orbit H x := mem_orbit x z
    rw [heq] at hm
    exact hm
  rcases hxmem with rfl | rfl <;> rcases hzmem with he | he
  · exact (hz he).elim
  · rw [heq, he]
  · rw [heq, he, Set.pair_comm]
  · exact (hz he).elim

public theorem fixes_short_of_generator_test (H : Subgroup He)
    (z : H) (g : Fin 3 → H)
    (htest : ∀ x : Fin 2058,
      (∀ i, (g i : He) • x = x ∨ (g i : He) • x = (z : He) • x) →
        (z : He) • x = x) :
    (z : He) ∈ fixingSubgroup He (shortPoints H) := by
  apply (mem_fixingSubgroup_iff He).mpr
  intro x hx
  by_contra hn
  apply hn
  apply htest x
  intro i
  have hmem := mem_orbit x (g i)
  rw [pair_orbit H x hx z hn] at hmem
  exact hmem

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankFourKernel
