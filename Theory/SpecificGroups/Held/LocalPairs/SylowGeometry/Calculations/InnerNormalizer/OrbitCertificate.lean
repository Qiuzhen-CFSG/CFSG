module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.Representative
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.Data
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.OrbitCertificate.Actions
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.OrbitCertificate.Checks

/-!
# Exact orbit cardinalities of the concrete Held representative

The 24 candidate components are invariant under the four published generators,
hence under their generated subgroup. A kernel-checked spanning forest gives
an actual subgroup element carrying each component root to each vertex.
Thus two vertices lie in the same orbit exactly when their component numbers
agree. The checked coordinate bijections identify each orbit with a finite
range whose size is the published `orbitSizeLabel`.

This proves the orbit identity with no assumed transitivity, group order or
Sylow identification. The normalizer argument consuming it is assembled in
`Calculations/InnerNormalizer`, independently of this module.

Source: ATLAS HeG1-p2058B0 and HeG1-max3W1; GLS3 Table 5.3p.
The exact word data are in `Calculations/Source/words.json`, the candidate
orbits in `InnerNormalizer/Source/orbits.json`, and the reproducible finite
certificate in `OrbitCertificate/Source`.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
namespace OrbitCertificate

private def componentPreservers : Subgroup He where
  carrier := {g | ∀ x : Fin 2058, color (g • x) = color x}
  one_mem' := by intro x; rw [one_smul]
  mul_mem' := by
    intro g h hg hh x
    rw [mul_smul, hg, hh]
  inv_mem' := by
    intro g hg x
    simpa only [smul_inv_smul] using (hg (g⁻¹ • x)).symm

private theorem color_invariant (g : representative) (x : Fin 2058) :
    color (g • x) = color x := by
  have h : representative ≤ componentPreservers := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩ y
    change color (representation (generator i) y) = color y
    rw [← action_eq]
    exact action_preserves_color i y
  exact h g.property x

private def gen (i : Fin 4) : representative := ⟨generator i, generator_mem i⟩

private theorem reach (x : Fin 2058) :
    ∃ g : representative, g • root (color x) = x := by
  suffices h : ∀ n : ℕ, ∀ y, depth y = n →
      ∃ g : representative, g • root (color y) = y from h (depth x) x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy
    rcases tree_valid y with he | ⟨hd, hc, hs⟩
    · exact ⟨1, by simpa using he.symm⟩
    · obtain ⟨g, hg⟩ := ih (depth (parent y)) (by omega) (parent y) rfl
      rw [hc] at hg
      refine ⟨gen (step y) * g, ?_⟩
      rw [mul_smul, hg]
      change representation (generator (step y)) (parent y) = y
      rw [← action_eq]
      exact hs

private theorem mem_orbit_iff_color (x y : Fin 2058) :
    y ∈ MulAction.orbit representative x ↔ color y = color x := by
  constructor
  · rintro ⟨g, rfl⟩
    exact color_invariant g x
  · intro hc
    obtain ⟨g, hg⟩ := reach x
    obtain ⟨h, hh⟩ := reach y
    rw [hc] at hh
    refine ⟨h * g⁻¹, ?_⟩
    change (h * g⁻¹) • x = y
    rw [mul_smul, ← hg, inv_smul_smul, hh]

private def orbitEquiv (x : Fin 2058) :
    MulAction.orbit representative x ≃ Fin (size (color x)) where
  toFun y := ⟨position y.val, by
    have h := (coordinates_valid y.val).1
    rwa [(mem_orbit_iff_color x y.val).mp y.property] at h⟩
  invFun i := ⟨vertex (color x) i.val,
    (mem_orbit_iff_color x _).mpr (enumeration_valid (color x) i).1⟩
  left_inv y := by
    apply Subtype.ext
    change vertex (color x) (position y.val) = y.val
    rw [← (mem_orbit_iff_color x y.val).mp y.property]
    exact (coordinates_valid y.val).2
  right_inv i := by
    apply Fin.ext
    exact (enumeration_valid (color x) i).2

end OrbitCertificate

/-- Every published label is the size of the orbit under the actual four-word
Held subgroup, with no order, transitivity or Sylow hypothesis. -/
public theorem orbitSizeLabel_eq_card_orbit (x : Fin 2058) :
    orbitSizeLabel x = Nat.card (MulAction.orbit representative x) := by
  rw [Nat.card_congr (OrbitCertificate.orbitEquiv x), Nat.card_fin,
    OrbitCertificate.size_eq_label]

end Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
