module

public import Theory.SpecificGroups.PSL4Three.ProperOvergroups.Line
public import Mathlib.GroupTheory.QuotientGroup.Finite
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Order.Atoms.Finite

/-!
# Reduction of the proper-overgroup cover for PSL₄(3)

Choose a maximal proper overgroup in the finite subgroup lattice. A solvable
one already has small layers. A reducible one lies in an actual projective
parabolic, leaving the nonsolvable irreducible maximal subgroups as the other
branch.

The coordinate-line parabolic and all subgroups of its conjugates are proved
in `Line`. The remaining parabolic calculations and the irreducible maximal
case are explicit premises below. Consequently this module does not yet prove
the unconditional proper-overgroup cover or the proper-K assertion.

Source application: Aschbacher–Smith, Theorem 0.1.2(4) and condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`. The finite-lattice reduction
assumes no maximal-subgroup classification.
-/

namespace Matrix.PSL4Three.ProperOvergroups

/-- A solvable subgroup needs no nonsolvable remaining layer. -/
public theorem hasSmallLayers_of_solvable
    (H : Type*) [Group H] [Group.IsSolvable H] : HasSmallLayers H :=
  Or.inl (Theory.GroupTheory.SolvableLayersEmbedding.of_solvable H _)

/-- Conditional assembly of the intrinsic cover. Both structural premises
must be proved before this yields the unconditional proper-overgroup theorem. -/
public theorem proper_overgroup_of_parabolics_and_irreducibles
    (hparabolic : ∀ W : Submodule (ZMod 3) Vec, W ≠ ⊥ → W ≠ ⊤ →
      HasSmallLayers (projectiveParabolic W))
    (hirreducible : ∀ M : Subgroup PSL, IsCoatom M → ¬ Reducible M →
      ¬ Group.IsSolvable M → HasSmallLayers M)
    (U : Subgroup PSL) (hU : U ≠ ⊤) :
    ∃ M : Subgroup PSL, U ≤ M ∧ HasSmallLayers M := by
  obtain ⟨M, hM, hUM⟩ := (eq_top_or_exists_le_coatom U).resolve_left hU
  by_cases hsolv : Group.IsSolvable M
  · let := hsolv
    exact ⟨M, hUM, hasSmallLayers_of_solvable M⟩
  by_cases hred : Reducible M
  · obtain ⟨W, hW0, hW1, hMW⟩ := hred
    exact ⟨projectiveParabolic W, hUM.trans hMW, hparabolic W hW0 hW1⟩
  · exact ⟨M, hUM, hirreducible M hM hred hsolv⟩

end Matrix.PSL4Three.ProperOvergroups
