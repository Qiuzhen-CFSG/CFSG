module
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockPoint

/-!
# Normalizer of the literal four-block residual

The normalizer of the embedded A₄ × A₄ in S₈ is exactly the stabilizer
of its two unordered four-letter blocks. Its characteristic two-core
V₄ × V₄ has those blocks as its two orbits, so every normalizer preserves
the block relation. Conversely the block stabilizer normalizes A₄ × A₄.

This supplies the core-preservation step in the contrary-fusion argument
of Aschbacher--Smith 12.6.19, printed p.828 of the combined manuscript
of 1 March 2004. The subgroup and permutation coordinates remain literal.
-/

public section
open Subgroup
namespace BinaryPermutation.TerminalOrthogonal.FourBlockPoint
open FourBlockResidual
open Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction

private theorem klein_orbit (i j : Fin 8) :
    i.val / 4 = j.val / 4 ↔ ∃ a b : Fin 4, kleinPerm a b i = j := by
  revert i j
  decide

private theorem normalizer_klein_le : normalizer (kleinGroup : Set S8) ≤ H := by
  intro g hg
  have step (p : S8) (hp : p ∈ normalizer (kleinGroup : Set S8))
      (i j : Fin 8) (hij : i.val / 4 = j.val / 4) :
      (p i).val / 4 = (p j).val / 4 := by
    obtain ⟨a,b,hab⟩ := (klein_orbit i j).mp hij
    have hc : p * kleinPerm a b * p⁻¹ ∈ kleinGroup :=
      (hp (kleinPerm a b)).mp ⟨a,b,rfl⟩
    obtain ⟨c,d,hcd⟩ := hc
    apply (klein_orbit (p i) (p j)).mpr
    refine ⟨c,d,?_⟩
    rw [←hcd]
    simpa using congrArg p hab
  intro i j
  constructor
  · intro hij
    have h := step g⁻¹ ((normalizer (kleinGroup : Set S8)).inv_mem hg) (g i) (g j) hij
    simpa using h
  · exact step g hg i j

/-- The actual two alternating four-letter factors determine their unordered blocks. -/
theorem residual_normalizer : normalizer (R : Set S8) = H := by
  apply le_antisymm _ H_normalizes_R
  have hn := normalizer_le_normalizer_characteristic_image R (pCore 2 R)
  change normalizer (R : Set S8) ≤ normalizer (R.pCoreIn 2 : Set S8) at hn
  rw [residual_core] at hn
  exact hn.trans normalizer_klein_le

end BinaryPermutation.TerminalOrthogonal.FourBlockPoint
