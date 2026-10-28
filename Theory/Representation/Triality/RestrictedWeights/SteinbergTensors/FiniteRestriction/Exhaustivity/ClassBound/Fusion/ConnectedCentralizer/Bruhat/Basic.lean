module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Reduction
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.RootProducts
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.NormalForm
public import Theory.AlgebraicGroup.Reductive.Defs
public import Theory.AlgebraicGroup.Tori.Maximal.theorem_1_4_3_b

/-!
# Geometric inputs for the toral-centralizer Bruhat argument

The coordinate and normal-form types refer to the actual root groups,
opposite root groups, and torus normalizer of `Geometry`. Their existence
remains separate from the centralizer deduction. `BorelCoverage` is the
weaker raw B–N–B theorem from which the unique root form must be derived.

Source: Steinberg 6.2(b), 6.3, and 8.3(c),
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
open Theory.AlgebraicGroup
namespace ConnectedCentralizer
universe u
variable {k : Type u} [Field k] [CharP k 2]
  {K : Variety k} [AlgebraicGroup K]

namespace Bruhat

/-- Ordered coordinates in the actual positive unipotent subgroup. -/
abbrev PositiveCoordinates (S : Geometry K) :=
  ToralRootCoordinates S.roots S.rootParameter S.roots.positive

/-- Actual Bruhat factors with the right factor in `U ∩ n⁻¹ U⁻ n`. -/
abbrev Form (S : Geometry K) :=
  ToralBruhatForm (RootSubgroupGenerated S.roots S.roots.positive)
    (RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive))
    S.torus.normalizer.toSubgroup

/-- Multiplication of the three actual Bruhat factors. -/
abbrev value (S : Geometry K) (f : Form S) : Variety.Point K := f.value

/-- Raw Borel–normalizer–Borel coverage, before root-factor refinement. -/
def BorelCoverage (S : Geometry K) : Prop :=
  ∀ g : Variety.Point K, ∃ b n c : Variety.Point K,
    b ∈ S.bigCell.data.B.toSubgroup ∧ n ∈ S.torus.normalizer.toSubgroup ∧
      c ∈ S.bigCell.data.B.toSubgroup ∧ g = b * n * c

/-- The supplied universal version is semisimple, so every radical is the
rank-zero torus. This supplies the reductivity premise of general B–N–B
coverage without invoking a conjugacy or Bruhat theorem. -/
theorem reductive [IsAlgClosed k] (S : Geometry K) : IsReductiveAlgebraicGroup K := by
  refine ⟨S.universal.1.1, ?_⟩
  intro R hR
  have h : R = ClosedSubgroup.bot := by
    apply SetLike.ext
    intro x
    change x ∈ R.toSubgroup ↔ x ∈ (⊥ : Subgroup (Variety.Point K))
    rw [S.universal.1.2 R hR]
  rw [h]
  exact closedSubgroup_bot_isTorus K

end Bruhat

end ConnectedCentralizer
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
