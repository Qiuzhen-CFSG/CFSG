module

public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient

/-!
# A square obstruction throughout the binary long-local radical

Write a long-local element as a five-root radical element times its actual
SL₂(2) image. If its commutator with C(1)D(1) has square one, that image has
square one. The check includes every radical parameter, so it applies to
arbitrary lifts of quotient elements, not just the chosen cubic lift.

This supplies the binary second-parabolic calculation for Aschbacher–Smith
2.3.9(7), printed p.526. The root and block coordinates are from the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Atlas.G2 Atlas.G2.PairStabilizer Atlas.G2.LieParabolicSetup
open scoped commutatorElement MatrixGroups

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem factor_square_image :
    ∀ (t : Fin 6 → ZMod 2) (M : SL(2,ZMod 2)), t 4 = 0 →
      (⁅rootC (1 : ZMod 2) * rootD 1, unipotentProduct t * blockHom M⁆ ^ 2).val
        (E 5) 0 = 0 → M ^ 2 = 1 := by
  decide +kernel

/-- The obstruction survives all perturbations by the five-root radical. -/
theorem binary_long_square_image (g : local₂ (F := ZMod 2))
    (hsq : ⁅rootC (1 : ZMod 2) * rootD 1, g.val⁆ ^ 2 = 1) :
    longSLHom g ^ 2 = 1 := by
  let u := g * (longSLSection (longSLHom g))⁻¹
  have hu : u ∈ (longSLHom (F := ZMod 2)).ker := by
    simp [u]
  rw [longSLHom_ker] at hu
  obtain ⟨t, ht, he⟩ := hu
  change unipotentProduct t = g.val * (blockHom (longSLHom g))⁻¹ at he
  have hg : g.val = unipotentProduct t * blockHom (longSLHom g) :=
    (eq_mul_inv_iff_mul_eq.mp he).symm
  apply factor_square_image t (longSLHom g) ht
  rw [← hg, hsq]
  rfl

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.G2.RelativeBlocks.SecondActor

end
