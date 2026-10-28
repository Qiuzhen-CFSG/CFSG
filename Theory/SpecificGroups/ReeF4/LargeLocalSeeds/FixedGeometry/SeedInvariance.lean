module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Invariance of the two concrete large Ree local factors

Every two-power automorphism of the large Ree group is inner, by the proved
signed-root-block automorphism calculation. If it preserves the positive
subgroup, its conjugating element belongs to that subgroup's normalizer,
which is the root Borel. The Borel lies in both full parabolics, and each
root-defined seed is normal in its own parabolic. Thus both seeds are fixed
individually.

The matrix-preserving equivalence `d.modelEquiv` transports the positive
subgroup, both seeds, and their normalizers to the supplied fixed group.
Consequently neither quotient identifications nor additional Sylow or
simplicity hypotheses are needed for this invariance statement.

Source: Aschbacher–Smith, F.1.12(I)(5), printed pp.263–264, and the
`N_S(L)`-invariant factors in the proof of 2.3.9(7), printed p.526 of
`refs/quasithin.pdf`. This module establishes the invariance ingredient;
the local quotient and radical calculations are separate results.
-/

public section

namespace ReeF4.LargeLocalSeeds

open Subgroup Parabolics Parabolics.OuterLocal.LargeAutomorphisms

/-- The positive subgroup's normalizer normalizes each actual fixed seed.
Normality is relative to the corresponding full parabolic. -/
theorem standardUnipotent_normalizer_le_seed_normalizer {m : ℕ}
    (d : LocalBlockInput m) (s : Side) :
    normalizer (standardUnipotent d : Set d.fixedGroup) ≤
      normalizer (standardSeed d s : Set d.fixedGroup) := by
  apply (map_le_map_iff_of_injective
    (f := d.modelEquiv.toMonoidHom) d.modelEquiv.injective).mp
  rw [map_equiv_normalizer_eq, map_equiv_normalizer_eq,
    modelEquiv_map_standardUnipotent, modelEquiv_map_standardSeed,
    unipotent_normalizer_eq_borel]
  exact (borel_le_parabolic m s).trans
    (parabolic_le_seed_normalizer_of_splitTorus m s (splitTorus_le_seed_normalizer m s))

/-- A two-power automorphism preserving the concrete positive subgroup
preserves each of the Suzuki and linear local factors individually. -/
theorem standardSeed_invariant_of_twoPower {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) (a : MulAut d.fixedGroup)
    (ha : ∃ n : ℕ, a ^ (2 ^ n) = 1)
    (hU : ∀ x, x ∈ standardUnipotent d ↔ a x ∈ standardUnipotent d) :
    ∀ s x, x ∈ standardSeed d s ↔ a x ∈ standardSeed d s := by
  obtain ⟨n, hn⟩ := ha
  have hpow : MulAut.congr d.modelEquiv a ^ (2 ^ n) = 1 := by
    rw [← map_pow, hn, map_one]
  obtain ⟨g, hg⟩ := inner_of_twoPower hm (MulAut.congr d.modelEquiv a) n hpow
  obtain ⟨g, rfl⟩ := (MulAut.congr_inner_iff d.modelEquiv a).mp ⟨g, hg.symm⟩
  have hg : g ∈ normalizer (standardUnipotent d) := mem_normalizer_iff.mpr hU
  intro s x
  exact mem_normalizer_iff.mp (standardUnipotent_normalizer_le_seed_normalizer d s hg) x

end ReeF4.LargeLocalSeeds

end
