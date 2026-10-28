module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.FrobeniusDifferential.TangentSpan.Parameters
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.FrobeniusDifferential.TangentSpan.DenseParameters.OppositeGeometry
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Roots

/-!
# Dominance reduced to positive-root tail normalization

Successive normalization of the actual positive root groups gives an ordered
coordinate cover. Apply that construction also to the opposite geometry,
which retains the same group and torus, to obtain the negative coordinate
cover. The root-product morphism then contains the dense opposite-Borel
product in its range.

The sole remaining geometric premise is explicitly stated below. Its root
order is exactly `ConnectedCentralizer.Bruhat.Coordinates.positiveOrder`,
unfolded here to avoid importing its independent assembly module. Neither
coordinate uniqueness nor tail separation is needed for dominance.

Source: Steinberg 6.2(b--c), `refs/KGroup/GLS3/Chapter2St2.tex`; the relative
normalization is the subgroup consequence of GLS3, Chapter 1, 1.12.7(b--c).
-/

noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Relative normalization for positive tails, applied in both choices of
root labels, gives a dominant morphism on the prescribed parameter space. -/
public theorem Geometry.exists_dense_root_parameter_morphism_of_positive_tail_normalization
    (S : Geometry K)
    (hnormal : ∀ R : Geometry K, ∀ a bs,
      (a :: bs).IsSuffix (List.ofFn fun i : Fin 12 =>
        R.rootIndex.symm (Triality.Standard.PositiveCoordinates.rootIndex i)) →
      (R.roots.rootSubgroup a).toSubgroup ≤ Subgroup.normalizer
        (RootSubgroupGenerated R.roots {b | b ∈ bs} : Set (Variety.Point K))) :
    ∃ f : Variety.Morphism S.rootProductParameterSpace K, Dense (Set.range f.toFun) := by
  have cover (R : Geometry K) : RootProductCover R.roots R.rootParameter R.roots.positive := by
    refine rootProductCover_of_suffixes R.roots R.rootParameter R.roots.positive
      (List.ofFn fun i : Fin 12 =>
        R.rootIndex.symm (Triality.Standard.PositiveCoordinates.rootIndex i)) ?_ ?_ (hnormal R)
    · exact List.nodup_ofFn.mpr (R.rootIndex.symm.injective.comp
        Triality.Standard.PositiveCoordinates.rootIndex_injective)
    · intro a
      rw [List.mem_ofFn, R.positive]
      constructor
      · rintro ⟨i, rfl⟩
        simpa only [Equiv.apply_symm_apply] using
          Triality.Standard.PositiveCoordinates.rootIndex_positive i
      · intro ha
        have hmem : R.rootIndex a ∈ Set.range Triality.Standard.PositiveCoordinates.rootIndex := by
          rw [Triality.Standard.PositiveCoordinates.range_rootIndex]
          exact ha
        obtain ⟨i, hi⟩ := hmem
        exact ⟨i, by simp only [hi, Equiv.symm_apply_apply]⟩
  exact S.exists_dense_root_parameter_morphism_of_covers
    (cover S) (S.negativeRootProductCover (cover S.opposite))

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
