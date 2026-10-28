module

public import Theory.GroupTheory.PCorePreimageCentralizer
public import Theory.AtlasPort.LinearGroups.G2.BinarySmallLocals
public import Theory.AtlasPort.LinearGroups.G2.DerivedParabolicGeneration
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Parameters

/-!
# Characteristic two for the marked G₂ parabolic pullbacks

The short binary parabolic is transported from the concrete order-two field.
For larger fields its characteristic-two calculation is an explicit input;
the long-parabolic calculation is unconditional. Intersecting with the actual
commutator range, then lifting through the actual two-group kernel, gives
characteristic two for both pullbacks in L.

This retains G₂(2)′ and every central two-cover permitted by the coordinates.
No surjectivity onto full G₂(2), faithful model map, or bound on the central
kernel is assumed. This is a conditional step for Aschbacher–Smith 2.3.9(7),
printed p.526, with the model alternatives from 1.1.5(3), pp.501–502.
The nonbinary short-parabolic premise must be discharged by source assembly.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2
open Subgroup Atlas.G2.LieParabolicSetup

private theorem first_model_centralizer_pCore
    {F : Type*} [Field F] [Finite F]
    (hshort : 2 < Nat.card F →
      centralizer (pCore 2 (parabolic₁ (F := F)) : Set (parabolic₁ (F := F))) ≤
        pCore 2 (parabolic₁ (F := F))) :
    centralizer (pCore 2 (parabolic₁ (F := F)) : Set (parabolic₁ (F := F))) ≤
      pCore 2 (parabolic₁ (F := F)) := by
  by_cases hq : 2 < Nat.card F
  · exact hshort hq
  have htwo : Nat.card F = 2 := by
    have := Finite.one_lt_card (α := F)
    omega
  let e := Atlas.G2.fieldEquiv (Atlas.G2.binaryFieldEquiv htwo)
  apply (Theory.Quasithin.centralizer_pCore_map_le_iff 2 e _).mp
  rw [(Atlas.G2.DerivedParabolicGeneration.map_binary_parabolics htwo).1,
    parabolic₁_binary]
  exact Atlas.G2.BinaryParabolicPair.firstParabolic_centralizer_pCore

namespace ParabolicCoordinates
variable {G : Type*} [Group G] {L S : Subgroup G} (d : ParabolicCoordinates L S)

/-- Both allowed model kernels are two-groups, including the entire center. -/
theorem model_kernel_isPGroup : IsPGroup 2 d.modelMap.ker := by
  rcases d.model_kernel with hk | ⟨_, hk, hZ, _⟩
  · rw [hk]
    exact IsPGroup.of_bot
  · rw [hk, hZ]
    exact pCore_isPGroup

/-- The short pullback has characteristic two, conditional only on the
nonbinary short-parabolic calculation. -/
theorem first_pullback_centralizer_pCore [Finite G]
    (hshort : 2 < Nat.card d.field →
      centralizer (pCore 2 (parabolic₁ (F := d.field)) : Set (parabolic₁ (F := d.field))) ≤
        pCore 2 (parabolic₁ (F := d.field))) :
    centralizer (pCore 2 (parabolic₁.comap d.modelMap) : Set (parabolic₁.comap d.modelMap)) ≤
      pCore 2 (parabolic₁.comap d.modelMap) := by
  let : d.modelMap.range.Normal := by rw [d.model_range]; infer_instance
  exact d.modelMap.centralizer_pCore_comap_of_normal_range d.model_kernel_isPGroup
    parabolic₁ (first_model_centralizer_pCore hshort)

/-- The long pullback has characteristic two in every allowed model case. -/
theorem second_pullback_centralizer_pCore [Finite G] :
    centralizer (pCore 2 (parabolic₂.comap d.modelMap) : Set (parabolic₂.comap d.modelMap)) ≤
      pCore 2 (parabolic₂.comap d.modelMap) := by
  let : d.modelMap.range.Normal := by rw [d.model_range]; infer_instance
  exact d.modelMap.centralizer_pCore_comap_of_normal_range d.model_kernel_isPGroup
    parabolic₂ Atlas.G2.EvenLocal.parabolic₂_centralizer_pCore

end ParabolicCoordinates
end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2

end
