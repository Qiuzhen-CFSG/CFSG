module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.PositiveTwoGroup
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.SplitGeneration
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.FixedBruhat
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.SeedInvariance

/-!
# Fixed positive subgroups and local factors in large Ree groups

The actual positive fixed subgroup is a two-group of odd index, hence a Sylow
two-subgroup. Fixed Bruhat geometry makes the join of the two root-defined local
factors a nontrivial normal subgroup; the supplied simplicity hypothesis gives
generation. This uses the fixed intersections themselves, with middle nodes
`{1, 2}` on the Suzuki side and end nodes `{0, 3}` on the linear side.

For the large parameters, every two-power automorphism is inner. If it preserves
the positive subgroup, its conjugating element lies in the root Borel, which
normalizes each local factor. The final assembly supplies Sylow status,
generation, and individual invariance together, in the form consumed by the
component seed construction. No quotient-identification hypotheses are needed;
the local quotient and radical calculations remain separate results.

Source: Aschbacher–Smith, F.1.12(I)(5) and (II), printed pp.263–264, and the
invariant local factors in 2.3.9(7), printed p.526 of `refs/quasithin.pdf`.
-/

public section
namespace ReeF4.LargeLocalSeeds

/-- Once its index is known to be odd, the actual fixed positive subgroup is
Sylow. The two-group property is proved from the concrete root matrices. -/
theorem exists_standardSylow_of_odd_index {m : ℕ} (d : LocalBlockInput m)
    (hindex : Odd (standardUnipotent d).index) :
    ∃ U : Sylow 2 d.fixedGroup, (U : Subgroup d.fixedGroup) = standardUnipotent d :=
  ⟨(standardUnipotent_isPGroup d).toSylow hindex.not_two_dvd_nat, rfl⟩

/-- The actual fixed positive subgroup is Sylow, with its odd index discharged
by the fixed Bruhat and normalizer calculations. This holds for every parameter. -/
theorem exists_standardSylow {m : ℕ} (d : LocalBlockInput m) :
    ∃ U : Sylow 2 d.fixedGroup, (U : Subgroup d.fixedGroup) = standardUnipotent d :=
  exists_standardSylow_of_odd_index d (FixedBruhat.standardUnipotent_index_odd d)

/-- The two actual fixed local factors generate the supplied simple fixed group. -/
theorem standardSeed_sup_eq_top {m : ℕ} (d : LocalBlockInput m)
    [IsSimpleGroup d.fixedGroup] :
    standardSeed d .suzuki ⊔ standardSeed d .linear = ⊤ :=
  FixedBruhat.standardSeed_sup_eq_top d

/-- Complete fixed geometry for the large Ree component seed construction.
The stability clause has the side-first order used by the component transport,
and concerns the same positive subgroup underlying the exhibited Sylow subgroup. -/
theorem exists_standardSylow_with_seed_geometry {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) [IsSimpleGroup d.fixedGroup] :
    ∃ U : Sylow 2 d.fixedGroup,
      (U : Subgroup d.fixedGroup) = standardUnipotent d ∧
      standardSeed d .suzuki ⊔ standardSeed d .linear = ⊤ ∧
      ∀ (s : Side) (a : MulAut d.fixedGroup),
        (∃ n : ℕ, a ^ (2 ^ n) = 1) →
        (∀ x, x ∈ standardUnipotent d ↔ a x ∈ standardUnipotent d) →
        ∀ x, x ∈ standardSeed d s ↔ a x ∈ standardSeed d s := by
  obtain ⟨U, hU⟩ := exists_standardSylow d
  exact ⟨U, hU, standardSeed_sup_eq_top d,
    fun s a ha hstable => standardSeed_invariant_of_twoPower hm d a ha hstable s⟩

end ReeF4.LargeLocalSeeds
end
