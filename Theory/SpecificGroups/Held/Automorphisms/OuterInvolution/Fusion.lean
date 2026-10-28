module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Normalization
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.FiniteFusion
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Assembly

/-!
# Outer involution fusion in the full Held permutation normalizer

The orbital graph bounds the full normalizer quotient by two. Normalizing
the existing Held Sylow therefore gives an ambient Sylow. Its outer coset
is exhausted by 1024 concrete words, and checked square witnesses and a
64-entry conjugation tree fuse its involutions to the published representative.
Sylow conjugacy and the two-coset decomposition give conjugacy by Held itself.

Faithfulness derives the implementing permutation's order from the order of
its action. Thus the theorem has exactly the hypotheses consumed by
`outerRow_of_representative`, without an extra order or realization premise.
The representative's fixed-subgroup structure remains an independent input
to the final source row. Source: GLS3 Table 5.3p and pp.260–261.
-/

public section
namespace Held.OuterInvolution.Fusion
open Subgroup LocalPairs LocalPairs.SylowGeometry

/-- Every outer involutory action implemented by the full permutation normalizer
is conjugate under an actual Held element to the fixed published action. -/
theorem conjugacy_coverage
    (n : normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))))
    (hn : orderOf (permutationGroup.normalizerMonoidHom n) = 2)
    (hout : ¬ ∃ g : He, MulAut.conj g = permutationGroup.normalizerMonoidHom n) :
    ∃ g : He, MulAut.congr (MulAut.conj g) action =
      permutationGroup.normalizerMonoidHom n := by
  obtain ⟨P, hP⟩ := exists_fullSylow
  apply coverage_of_sylow P ?_ n hn hout
  intro y hy hyout
  have hymem : (y : PermutationNormalizer) ∈ fullSylow := hP ▸ y.property
  obtain ⟨i, hi⟩ := fullSylow_oddWord_coverage outer_mem_fullSylow y hymem hyout
  rw [← hi] at hy ⊢
  exact oddWord_isCovered i hy

/-- Application to the literal source-row assembler: only the independent
fixed-subgroup covering calculation remains as input. -/
theorem outerRow_of_fixed_cover
    (hfixed : Theory.GroupTheory.HasQuasisimpleNormalOfIndexTwo action.fixedSubgroup 3) :
    InvolutionFixedData.OuterRow :=
  outerRow_of_representative hfixed conjugacy_coverage

end Held.OuterInvolution.Fusion
