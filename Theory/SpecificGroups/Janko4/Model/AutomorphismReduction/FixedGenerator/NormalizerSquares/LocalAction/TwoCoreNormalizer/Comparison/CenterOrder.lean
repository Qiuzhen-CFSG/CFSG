module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.QuotientAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CenterOrder.Reduction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CenterOrder.InvolutionCensus
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.TwoGroup

/-!
# Center order for the literal J₄ two-core

Let C be the literal centralizer of `matrixUnitA` in `matrixGroup`, and let
Q = O₂(C). The distinguished involution belongs to Z(Q), giving the lower
bound two. The certified max2 generators generate C, so their relative seed
normal closure maps to a normal two-subgroup N of C and hence lies in Q.

Every element centralizing Q therefore centralizes N. The full relative
centralizer census says that such an element is either the identity or the
distinguished involution, giving the upper bound two. All local premises are
discharged by the imported concrete certificates. No centralizer-control or
extraspeciality hypothesis, or identification of N with Q, is required.

Source: GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. This proves the center-order consequence
of the table's 2A centralizer shape for the literal matrix two-core.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison

open TwoCoreCentralizerData

/-- The center of the actual two-core of the literal involution centralizer
has order two. The concrete local facts discharge every premise. -/
theorem center_card_two : Nat.card (Subgroup.center involutionTwoCore) = 2 := by
  let e : localSubgroup ≃* involutionCentralizer :=
    (MulEquiv.subgroupCongr localSubgroup_eq_top).trans Subgroup.topEquiv
  let N := localNormalClosure.map e.toMonoidHom
  have hNn : N.Normal := localNormalClosure_normal.map e.toMonoidHom e.surjective
  have hNp : IsPGroup 2 N := localNormalClosure_isPGroup.map e.toMonoidHom
  have hN : N ≤ involutionTwoCore := le_sSup ⟨hNn, hNp⟩
  apply center_card_two_of_centralizer_le
  intro z hz
  have hze : e.symm z ∈ Subgroup.centralizer
      (localNormalClosure : Set localSubgroup) := by
    intro n hn
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      (Subgroup.centralizer_le hN hz) (e n) (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
  have he : e subgroupInvolution = centralInvolution := rfl
  rcases localSeedCentralizer_cases (e.symm z) hze with hi | hi
  · have hz1 : z = 1 := by
      simpa only [e.apply_symm_apply, map_one] using congrArg e hi
    rw [hz1]
    exact (Subgroup.zpowers centralInvolution).one_mem
  · have hza : z = centralInvolution := by
      simpa only [e.apply_symm_apply, he] using congrArg e hi
    rw [hza]
    exact Subgroup.mem_zpowers centralInvolution

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison
