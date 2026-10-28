module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.FixedGeometry.BruhatCoverage.SplitCoverage.RootConditions

/-!
# Weyl words acting on the actual binary root matrices

Simple-root conjugation extends by word induction to an opposition-preserving
permutation of all roots. The premise is precisely the local matrix relation
GLS3 1.12.1(h), in `refs/KGroup/GLS3/Chapter1.tex`.
-/

public section
noncomputable section
namespace ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RadicalCoordinates LargeLocalSeeds Subgroup
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- The action of a Weyl word on roots preserves opposition. -/
theorem weyl_root_conjugation_of_simple (hconj : BinarySimpleRootConjugation)
    {n : SplitGroup 0} (hn : n ∈ splitWeylSubgroup) :
    let _ := typeF4RootPairing.indexNeg
    ∃ σ : Equiv.Perm F4Chevalley.Root,
      (∀ r, σ (-r) = -σ r) ∧
      ∀ r t, n * rootGeneratorInGroup 0 r t * n⁻¹ = rootGeneratorInGroup 0 (σ r) t := by
  let _ := typeF4RootPairing.indexNeg
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i), ?_, hconj i⟩
    intro r
    apply typeF4RootPairing.root.injective
    have hrootneg (q : F4Chevalley.Root) :
        typeF4RootPairing.root (-q) = -typeF4RootPairing.root q := by
      simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
        RootPairing.reflection_apply_self]
    simp only [hrootneg, RootPairing.root_reflectionPerm, map_neg]
  | one =>
    exact ⟨Equiv.refl _, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨σ, hσneg, hσ⟩ := hx
    obtain ⟨τ, hτneg, hτ⟩ := hy
    refine ⟨τ.trans σ, ?_, ?_⟩
    · intro r
      change σ (τ (-r)) = -σ (τ r)
      rw [hτneg, hσneg]
    · intro r t
      change _ = rootGeneratorInGroup 0 (σ (τ r)) t
      calc
        _ = x * (y * rootGeneratorInGroup 0 r t * y⁻¹) * x⁻¹ := by group
        _ = _ := by rw [hτ, hσ]
  | inv x _ hx =>
    obtain ⟨σ, hσneg, hσ⟩ := hx
    refine ⟨σ.symm, ?_, ?_⟩
    · intro r
      apply σ.injective
      rw [σ.apply_symm_apply, hσneg, σ.apply_symm_apply]
    · intro r t
      have he := hσ (σ.symm r) t
      rw [σ.apply_symm_apply] at he
      calc
        _ = x⁻¹ * (x * rootGeneratorInGroup 0 (σ.symm r) t * x⁻¹) * x := by
          rw [he, inv_inv]
        _ = _ := by group

end ReeF4.Parabolics.Binary.FixedGeometry.BruhatCoverage
