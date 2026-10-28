module

public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Inner torus actions and the actual displacement subgroup

Suppose V acts on L through specified elements of Z ≤ L, and X ≤ L.
If the X-fixed elements of Z centralize L, the X-fixed elements of V are
exactly its L-centralizer. The displacement of V is contained in [Z,X].
If X is transitive on the nonidentity elements of [Z,X], any nontrivial
V-action on L forces equality of the two displacement groups.

All actions and witnesses use literal ambient conjugation. This is the
inner-action step in Aschbacher–Smith E.6.7(3), printed p.246.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupAction.InnerTorusDisplacement
variable {G : Type*} [Group G] (L Z V X : Subgroup G)

/-- Agreement of inner conjugations identifies the actual fixed subgroup. -/
theorem fixed_eq
    (hXL : X ≤ L)
    (hinner : ∀ v ∈ V, ∃ z ∈ Z, ∀ l ∈ L, z*l*z⁻¹ = v*l*v⁻¹)
    (hfixed : Z ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G)) :
    V ⊓ centralizer (X : Set G) = V ⊓ centralizer (L : Set G) := by
  apply le_antisymm
  · rintro v ⟨hv, hvX⟩
    obtain ⟨z, hz, he⟩ := hinner v hv
    have hzX : z ∈ centralizer (X : Set G) := by
      apply mem_centralizer_iff.mpr
      intro x hx
      have h := he x (hXL hx)
      rw [← mem_centralizer_iff.mp hvX x hx, mul_inv_cancel_right] at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    refine ⟨hv, ?_⟩
    apply mem_centralizer_iff.mpr
    intro l hl
    have h := (he l hl).symm
    rw [← mem_centralizer_iff.mp (hfixed ⟨hz, hzX⟩) l hl,
      mul_inv_cancel_right] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · exact inf_le_inf_left _ (centralizer_le hXL)

/-- Transitivity on the intrinsic moved line makes every nontrivial inner
actor family move that same line; normalization of V is unnecessary here. -/
theorem moved_eq
    (hXL : X ≤ L)
    (hinner : ∀ v ∈ V, ∃ z ∈ Z, ∀ l ∈ L, z*l*z⁻¹ = v*l*v⁻¹)
    (hfixed : Z ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G))
    (htrans : ∀ a ∈ ⁅Z,X⁆, a ≠ 1 → ∀ b ∈ ⁅Z,X⁆, b ≠ 1 →
      ∃ x ∈ X, x*a*x⁻¹ = b)
    (hescape : ¬ V ≤ centralizer (L : Set G)) : ⁅V,X⁆ = ⁅Z,X⁆ := by
  have hle : ⁅V,X⁆ ≤ ⁅Z,X⁆ := by
    apply commutator_le.mpr
    intro v hv x hx
    obtain ⟨z, hz, he⟩ := hinner v hv
    have hh : ⁅v,x⁆ = ⁅z,x⁆ := by
      simp only [commutatorElement_def]
      rw [← he x (hXL hx)]
    rw [hh]
    exact commutator_mem_commutator hz hx
  have hne : ⁅V,X⁆ ≠ ⊥ := by
    intro he
    have hv := commutator_eq_bot_iff_le_centralizer.mp he
    apply hescape
    have hfx := fixed_eq L Z V X hXL hinner hfixed
    rw [inf_eq_left.mpr hv] at hfx
    exact hfx ▸ inf_le_right
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  apply le_antisymm hle
  intro b hb
  by_cases hb1 : b = 1
  · simpa only [hb1] using (one_mem ⁅V,X⁆)
  obtain ⟨x, hx, he⟩ := htrans a (hle a.property) (fun hh => ha (Subtype.ext hh)) b hb hb1
  rw [← he]
  exact ((normalizer_commutator_ge_right V X hx) a).mp a.property

end Theory.GroupAction.InnerTorusDisplacement
