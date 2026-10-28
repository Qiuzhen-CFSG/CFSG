module

public import Stellmacher.SectionEleven.UniqueDihedralInvolution
public import Theory.GroupTheory.InvolutionCentralizerFourRecognition

/-!
# The dihedral terminal case of Section 11

Under Hypothesis Two, suppose the first local subgroup is S4 and is exactly
the normalizer of its two-core. Then the ambient Sylow two-subgroup is
dihedral or semidihedral. The strict inclusion hypothesis from the
unique-maximal branch is retained in the interface.

The involution extraction theorem uses the S4 core calculation and the
two-group normalizer condition to find a noncentral core involution whose
centralizer in the ambient Sylow subgroup has order four. The reusable
recognition theorem then supplies the required dihedral equivalence or
semidihedral presentation. Its cyclic-complement prerequisite proves the
commutator/Frattini calculation, rather than assuming the classification.
Neither the pair classification (8.2) nor the core-normalizer equality is
inferred here: the needed model and equality are explicit hypotheses.

Source: Stellmacher, N-Groups, Section 11, case (I), lines 2082–2087 of
`refs/latex/stellmacher-n-group.tex`, citing Gorenstein, Finite Groups (1968),
Section 5.4.5 for the two-group calculation.
-/

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven Later

universe u

public theorem unique_dihedral_terminal
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (h : HypothesisTwo H S0 S P1 P2)
    (_hne : S ≠ (S0 : Subgroup H))
    (hModel : IsModel P1 S4)
    (hNormalizer : Subgroup.normalizer (twoCoreIn P1 : Set H) = P1) :
    IsDihedralGroup S0 ∨ IsSemidihedralGroup S0 := by
  obtain ⟨x, _, hx, hxZ, hxC⟩ := exists_core_involution_centralizer_four
    S0 S P1 h.fiveOne.S_le_S0 h.fiveOne.P1_mem.1.2.1 hModel hNormalizer
  exact exists_dihedral_or_semidihedral_of_involution_centralizer_card_four
    S0.isPGroup' x hx hxZ hxC

end Stellmacher.SectionEleven
