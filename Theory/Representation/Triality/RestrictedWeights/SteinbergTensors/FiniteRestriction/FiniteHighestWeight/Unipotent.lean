module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Contracts
public import Theory.AlgebraicGroup.Unipotent.DefiningCharacteristic

/-!
# Positive unipotent points in the D4 elementary group

The positive root subgroup is the actual unipotent radical in the supplied
Borel geometry. Its points form a two-group in characteristic two. Therefore
all of its graph-field fixed points already belong to the subgroup generated
by two-elements; restricting to that elementary subgroup loses none of them.
A rational highest vector is fixed by the whole positive root subgroup, hence
also by its finite intersection. This proves one direction of the finite
highest-line calculation, without any bound on the highest weight.

Sources: GLS3, Theorem 2.8.2; Steinberg, `Chapter2St2.tex`, Sections 12--13.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
/-- The elementary inclusion retains both literal subgroup inclusions. -/
theorem inclusion_injective (S : Geometry K) (n : ℕ) :
    Function.Injective (S.inclusion n) :=
  Subtype.coe_injective.comp Subtype.coe_injective

/-- The full positive-root subgroup has two-power element orders. -/
theorem positiveRoots_isPGroup (S : Geometry K) :
    IsPGroup 2 (RootSubgroupGenerated S.roots S.roots.positive) := by
  rw [← S.bigCell.data.positive_witness.root_generated]
  exact S.bigCell.data.positive_witness.unipotent.isPGroup_of_unipotent
    S.bigCell.data.positive_witness.radical.2.1 2

/-- The positive subgroup used by finite restriction is a two-group. This
holds even before finiteness is supplied by a positive exponent. -/
theorem positiveUnipotent_isPGroup (S : Geometry K) (n : ℕ) :
    IsPGroup 2 (positiveUnipotent S n) :=
  (positiveRoots_isPGroup S).comap_of_injective (S.inclusion n)
    (inclusion_injective S n)

/-- Every positive unipotent graph-field fixed point lies in the elementary
subgroup. No equality of the whole elementary and fixed-point groups is used. -/
theorem positiveFixed_le_elementary (S : Geometry K) (n : ℕ) :
    (RootSubgroupGenerated S.roots S.roots.positive).comap
      (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype ≤
        graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n := by
  intro x hx
  have hU := (positiveRoots_isPGroup S).comap_of_injective
    (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype
    Subtype.coe_injective
  obtain ⟨m, hm⟩ := hU ⟨x, hx⟩
  apply Subgroup.subset_closure
  exact ⟨m, congrArg Subtype.val hm⟩

/-- The elementary positive subgroup maps onto all positive unipotent fixed
points. This is the precise comparison needed for finite root calculations. -/
theorem map_positiveUnipotent (S : Geometry K) (n : ℕ) :
    (positiveUnipotent S n).map
      (graphFieldElementarySubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype =
        (RootSubgroupGenerated S.roots S.roots.positive).comap
          (graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n).subtype := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro x hx
    exact ⟨⟨x, positiveFixed_le_elementary S n hx⟩, hx, rfl⟩

/-- A highest vector is fixed by every positive root element, using
rationality and the absence of nontrivial characters of a unipotent group. -/
theorem highestVector_fixed_positiveRoots (S : Geometry K) (A : RationalFactor K)
    {a : Weight} {v : A.Space}
    (hv : HasHighWeight A.action S.bigCell.data.B S.torus v (S.coordinateEmbedding a))
    (g : Variety.Point K) (hg : g ∈ RootSubgroupGenerated S.roots S.roots.positive) :
    (A.action.action g).1 v = v := by
  apply invariantLine_fixed_of_unipotent_subgroup A.action A.irreducible.1
    S.bigCell.data.B S.bigCell.data.positive_witness.unipotent v hv.1
    S.bigCell.data.positive_witness.radical.1
    S.bigCell.data.positive_witness.radical.2.1
  rwa [← S.bigCell.data.positive_witness.root_generated] at hg

/-- A rational highest vector is fixed on restriction to the finite positive
subgroup, for every exponent and without a restricted-weight hypothesis. -/
theorem highestVector_fixed_positiveUnipotent (S : Geometry K) (A : RationalFactor K)
    {a : Weight} {v : A.Space}
    (hv : HasHighWeight A.action S.bigCell.data.B S.torus v (S.coordinateEmbedding a))
    (n : ℕ) (g : positiveUnipotent S n) :
    (A.restrict (S.inclusion n)).ρ g.val v = v :=
  highestVector_fixed_positiveRoots S A hv (S.inclusion n g.val) g.property
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
