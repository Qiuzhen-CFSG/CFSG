module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.Reduction
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.Projection
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.CommutatorGeneration
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.Nonabelian

/-!
# Linear-side local calculations for the large Ree family

For every supplied exceptional Ree twist over a field of size 2^(2m+1), m ≥ 1,
the root radical of the end-node seed is its intrinsic two-core. This core is
nontrivial and self-centralizing inside the seed, the seed is perfect, and its
quotient by the core is the actual PSL₂ over the specified coefficient field.
The iterated commutator [[O₂(K),K],O₂(K)] is nontrivial.

The concrete fixed Levi projection has exactly the root radical as kernel,
which is a two-group by the positive unitriangular calculation. The root and
torus relations give R ≤ [R,K], and two fixed middle-subsystem words do not
commute. These proved inputs discharge every premise of the assembly in
`Reduction`. The first isomorphism theorem supplies the quotient equivalence
and its formula on representatives. No ambient simplicity hypothesis is needed.

These are the linear local-factor calculations used by the source assembly;
the Sylow geometry and the separate radical order q^11 are not asserted here.

Source: Aschbacher–Smith, F.1.12(I)(5) and (II), printed pp.263–264,
and 2.3.9(7), printed p.526.
-/

public section

namespace ReeF4.LargeLocalSeeds

open Subgroup

/-- All six intrinsic linear-seed conclusions, with the concrete projection
and radical root calculations fully discharged. -/
theorem linearCore_conclusions {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    seedRadical d .linear = pCore 2 (standardSeed d .linear) ∧
      pCore 2 (standardSeed d .linear) ≠ ⊥ ∧
      centralizer (pCore 2 (standardSeed d .linear) : Set (standardSeed d .linear)) ≤
        pCore 2 (standardSeed d .linear) ∧
      Group.IsPerfect (standardSeed d .linear) ∧
      Nonempty ((standardSeed d .linear ⧸ pCore 2 (standardSeed d .linear)) ≃*
        LinearQuotient m) ∧
      ⁅⁅pCore 2 (standardSeed d .linear), (⊤ : Subgroup (standardSeed d .linear))⁆,
        pCore 2 (standardSeed d .linear)⁆ ≠ ⊥ := by
  obtain ⟨f, hf, hker, hP⟩ := exists_linearSeedProjection hm d
  obtain ⟨x, y, hx, hy, hxy⟩ := seedRadical_linear_exists_noncommuting hm d
  exact linearCore_conclusions_of_root_calculations hm d f hf hker hP
    (seedRadical_linear_le_commutator hm d) x y hx hy hxy

/-- The original root-defined radical is exactly the intrinsic two-core. -/
theorem seedRadical_linear_eq_twoCore {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    seedRadical d .linear = pCore 2 (standardSeed d .linear) :=
  (linearCore_conclusions hm d).1

/-- The two-core of the linear seed contains nonidentity radical elements. -/
theorem linearCore_ne_bot {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    pCore 2 (standardSeed d .linear) ≠ ⊥ :=
  (linearCore_conclusions hm d).2.1

/-- Self-centralization is relative to the linear seed. -/
theorem linearCore_centralizer_le {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    centralizer (pCore 2 (standardSeed d .linear) : Set (standardSeed d .linear)) ≤
      pCore 2 (standardSeed d .linear) :=
  (linearCore_conclusions hm d).2.2.1

/-- The large-field linear local factor is perfect, as in F.1.12(II). -/
theorem linearSeed_perfect {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    Group.IsPerfect (standardSeed d .linear) :=
  (linearCore_conclusions hm d).2.2.2.1

/-- The actual projection induces an equivalence from the intrinsic core
quotient to PSL₂ over the specified Ree coefficient field. -/
noncomputable def linearCoreQuotientEquiv {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) :
    (standardSeed d .linear ⧸ pCore 2 (standardSeed d .linear)) ≃*
      LinearQuotient m :=
  linearCoreQuotientEquivOfProjection hm d (LinearProjection.projection hm d)
    (LinearProjection.projection_surjective hm d) (LinearProjection.projection_ker hm d)
    (seedRadical_isPGroup d .linear)

/-- On representatives the core quotient equivalence is the concrete Levi projection. -/
@[simp] theorem linearCoreQuotientEquiv_mk {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    (x : standardSeed d .linear) :
    linearCoreQuotientEquiv hm d
      (QuotientGroup.mk' (pCore 2 (standardSeed d .linear)) x) =
        LinearProjection.projection hm d x := by
  exact linearCoreQuotientEquivOfProjection_mk hm d (LinearProjection.projection hm d)
    (LinearProjection.projection_surjective hm d) (LinearProjection.projection_ker hm d)
    (seedRadical_isPGroup d .linear) x

/-- The noncommuting fixed radical words detect the iterated core commutator
used in the local block exclusion. All commutators are taken inside the seed. -/
theorem linearCore_iterated_commutator_ne_bot {m : ℕ} (hm : 1 ≤ m)
    (d : LocalBlockInput m) :
    ⁅⁅pCore 2 (standardSeed d .linear), (⊤ : Subgroup (standardSeed d .linear))⁆,
      pCore 2 (standardSeed d .linear)⁆ ≠ ⊥ :=
  (linearCore_conclusions hm d).2.2.2.2.2

end ReeF4.LargeLocalSeeds

end
