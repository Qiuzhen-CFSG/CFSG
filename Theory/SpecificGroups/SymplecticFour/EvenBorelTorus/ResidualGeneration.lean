module

public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Alignment
public import Theory.SpecificGroups.SymplecticFour.RootTori

/-!
# The unipotent Sylow lies in the higher-field Borel residual

Every diagonal torus element has odd order and lies in O²(B₀). The
root-torus commutator formula, valid when the field has more than two
elements, puts all four positive root subgroups in that residual. The
explicit four-root coordinates then contain the whole unipotent subgroup.
Conjugating to any specified Sylow gives O₂(O²(N(S)))=S.

This supplies the previously separate generation step in the symplectic
Borel calculation. Source application: Aschbacher–Smith, proof of 13.8.20,
printed p.954/PDF p.971. The root calculations and coordinates are the
actual matrices from RootTori and Sylow.CentralRootGeometry.Coordinates.
-/

public section
open Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The four positive root groups generate the full unipotent group inside the residual. -/
theorem unipotent_le_residual {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    unipotent (F := F) ≤ residual := by
  have hgt : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_le_of_lt (by decide : 2 ≤ 2 ^ 1) (Nat.pow_lt_pow_right (by decide) hn)
  have hdiag (a b : Fˣ) : diagonalTorus a b ∈ residual := by
    have hh := torusSection_mem_residual hF (a, a * b)
    change diagonalTorus a (a⁻¹ * (a * b)) ∈ residual at hh
    simpa only [inv_mul_cancel_left] using hh
  have hnorm : borel (F := F) ≤ normalizer ((residual (F := F) : Subgroup (Sp F)) : Set (Sp F)) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pResidual 2 (borel (F := F))).le_normalizer_map (borel (F := F)).subtype
  have hroot (r : Fin 8) (hr : r = 0 ∨ r = 2 ∨ r = 4 ∨ r = 6) :
      RootSubgroup.group (F := F) r ≤ residual := by
    have hrB : RootSubgroup.group (F := F) r ≤ borel := by
      intro x hx
      obtain ⟨u, rfl⟩ := (RootSubgroup.mem_group_iff r x).mp hx
      exact ((mem_unipotent_iff _).mp (positive_root_mem_unipotent r u hr)).1
    have htR : RootTori.torus (F := F) r ≤ residual := by
      rintro x ⟨s, rfl⟩
      exact hdiag _ _
    rw [← RootTori.commutator_eq r hgt]
    exact (commutator_mono hrB htR).trans
      (le_normalizer_iff_commutator_le_right.mp hnorm)
  intro u hu
  obtain ⟨⟨b, a, w, v⟩, he⟩ := CentralRootGeometry.element_surjective ⟨u, hu⟩
  have hv := congrArg Subtype.val he
  change (CentralRootGeometry.element b a w v : Sp F) = u at hv
  rw [← hv]
  change rootElement 6 b * rootElement 0 (a + b * w) * rootElement 4 w * rootElement 2 v ∈ _
  exact mul_mem (mul_mem (mul_mem
    (hroot 6 (by simp) ((RootSubgroup.mem_group_iff _ _).mpr ⟨b, rfl⟩))
    (hroot 0 (by simp) ((RootSubgroup.mem_group_iff _ _).mpr ⟨a + b * w, rfl⟩)))
    (hroot 4 (by simp) ((RootSubgroup.mem_group_iff _ _).mpr ⟨w, rfl⟩)))
    (hroot 2 (by simp) ((RootSubgroup.mem_group_iff _ _).mpr ⟨v, rfl⟩))

/-- Transport the containment to the Borel at the specified Sylow. -/
theorem sylow_le_residualAt {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) : (S : Subgroup (Sp F)) ≤ residualAt S := by
  obtain ⟨g, hU, _, hR⟩ := residualAt_conjugate hF (by omega) S
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) (unipotent_le_residual hF hn)
  rwa [hU, hR] at hh

/-- Over a higher even field, the residual has the same full Sylow two-core as the Borel. -/
theorem residualAt_twoCore_eq_sylow {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) : (residualAt S).pCoreIn 2 = S := by
  rw [residualAt_twoCoreIn hF (by omega) S, inf_eq_left.mpr (sylow_le_residualAt hF hn S)]

end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
