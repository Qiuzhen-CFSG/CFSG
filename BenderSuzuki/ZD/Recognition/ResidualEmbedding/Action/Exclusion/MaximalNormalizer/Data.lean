module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.Data.Geometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.Data.Selection
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.MaximalNormalizer.Data.SevenD

/-!
# Distinguished maximal-normalizer data from the first stage

Propositions 7.8 and 7.9 supply distinguished triple transport and exclude
invariant Sylow subgroups of D. Lemma 7.3 starts the admissible family;
finite maximization and the normalizer condition give its strict invariant
Sylow enlargement. Section 3 puts [E,z] in the odd core of E, allowing
solvable coprime action on that commutator to establish (7D).

All fields of the local normalizer input are constructed here with the
original prime, distinguished involution, cosets and relative normalizers.
The subsequent local quotient and ZJ argument remains in its own consumer.

Source: GLS, Volume 4, Chapter 2, Propositions 7.8–7.9 and the second-stage
setup preceding Lemma 7.10.
-/

namespace BenderSuzuki.ZD

open Theory.GroupTheory PFAppendixIII

variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The complete maximal-normalizer input for every point selected by
Proposition 7.2. No additional geometry, oddness or Sylow premise remains. -/
public theorem actionMaximalNormalizerData_of_firstStage
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hc : ActionCounting Z M) (d : ActionMaximalCounterexample Z M)
    (h64 : ActionCorollary64 d.data)
    (h72 : Theorem4bProposition72 d.data.toTheorem4bSixA)
    {beta : G ⧸ M} (hb : beta ∈ d.data.toTheorem4bSixA.kFixedPoints)
    (hne : beta ≠ QuotientGroup.mk 1)
    (_htheta : corollary64Theta d.data.p (theorem4bSection7D M beta) = ⊥) :
    Nonempty (ActionMaximalNormalizerData d.data beta) := by
  obtain ⟨a, hmax, R, hRsyl, hP₁R, htR, hlt⟩ :=
    action_maximal_admissibleQ_sylow h r hc d h64 h72 hb hne
  refine ⟨{
    chosen := a, maximal := hmax, R := R, hRsylow := hRsyl,
    hP₁R := hP₁R, htNormR := htR, hP₁card_lt_R := hlt,
    sevenD := action_sevenD h.disconnected
      (actionSectionThree_of_minimalCounterexample h r) d.data hb hne,
    triple_bound := ?_ }⟩
  intro w hw gamma delta hwg hgd P hP hPtriple
  exact action_triple_pSubgroup_card_le h.disconnected
    (d.two_transitive_of_proposition72 h.disconnected hc h64 h72)
    d.data hne a.hP₁sylow hw hwg hgd hP hPtriple

end BenderSuzuki.ZD
