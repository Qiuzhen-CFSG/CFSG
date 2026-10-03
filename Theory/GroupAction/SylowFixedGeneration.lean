module
public import Theory.GroupAction.Defs
public import Mathlib.GroupTheory.Sylow


/-!
# Transport of fixed-subgroup generation between Sylow images

For any homomorphism from P to an acting group A, generation by A-translates
of the fixed subgroup of one Sylow image implies the same for every Sylow
image at that prime. Only finiteness of the set of Sylow subgroups is needed;
the action need not be faithful and the homomorphism need not be surjective.

Sylow conjugacy changes its fixed subgroup by the image of the conjugator.
Translate each fixed vector accordingly and absorb the inverse image of the
conjugator into its orbit actor. Thus every old generator is a new generator.
This is the source-neutral transport used for the arbitrary next Sylow in
Stellmacher (9.8), printed pp.55–56.
-/

namespace Subgroup
open scoped Pointwise

public theorem fixed_generation_of_sylow
    {P A W : Type*} [Group P] [Group A] [Group W]
    [MulDistribMulAction A W] {p : ℕ} [Fact p.Prime] [Finite (Sylow p P)]
    (f : P →* A) (S₀ S₁ : Sylow p P)
    (hgen : (⊤ : Subgroup W) = closure {x : W | ∃ actor : A, ∃ point,
      point ∈ FixedPoints.subgroup ((S₀ : Subgroup P).map f) W ∧ x = actor • point}) :
    (⊤ : Subgroup W) = closure {x : W | ∃ actor : A, ∃ point,
      point ∈ FixedPoints.subgroup ((S₁ : Subgroup P).map f) W ∧ x = actor • point} := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P S₀ S₁
  have hsub : (S₁ : Subgroup P) = (S₀ : Subgroup P).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  apply le_antisymm ?_ le_top
  rw [hgen]
  apply (closure_le _).mpr
  rintro x ⟨actor, point, hpoint, rfl⟩
  apply subset_closure
  refine ⟨actor * (f g)⁻¹, f g • point, ?_, ?_⟩
  · intro image
    obtain ⟨s, hs, heq⟩ := image.property
    change (image : A) • (f g • point) = f g • point
    rw [← heq]
    rw [hsub] at hs
    obtain ⟨r, hr, rfl⟩ := hs
    change f (g * r * g⁻¹) • (f g • point) = f g • point
    rw [map_mul, map_mul, map_inv, mul_smul, mul_smul, inv_smul_smul]
    rw [show f r • point = point from hpoint ⟨f r, mem_map_of_mem f hr⟩]
  · simp only [mul_smul, inv_smul_smul]

end Subgroup
