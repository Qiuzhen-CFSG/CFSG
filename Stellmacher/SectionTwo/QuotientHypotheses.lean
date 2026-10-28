module

public import Stellmacher.SectionTwo.QuotientAction
public import Stellmacher.SectionTwo.VSubgroupElementaryAbelian

/-!
# Section 1 hypotheses for the Section 2 quotient

The Section 2 quotient G/C_G(V), acting on V by the named conjugation
action, satisfies all four Section 1 hypotheses whenever the image of
the elementary Thompson subgroup J(S) is nontrivial. The elementary
abelian instance on V is precisely the one supplied by the proved
Section 2 elementary-abelian theorem.

Solvability descends along the quotient map. Its nontrivial J(S) image
lies in the mapped Sylow 2-subgroup, whose nontrivial 2-power order forces
even quotient order. Faithfulness is the quotient action theorem and
triviality of the 2-core is Stellmacher (2.1).

This is the context needed for the classification application in
Stellmacher (2.2), Journal of Algebra 190 (1997), p.20, in
`refs/latex/stellmacher-n-group.tex`. It uses no classification result.
-/

namespace Stellmacher.SectionTwo
universe u

public theorem quotientConjugationAction_hypotheses
    {G : Type u} [Group G] [Finite G] (h : Hypotheses G) (S : Sylow 2 G)
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q) (hker : q.ker = cSubgroup S)
    (hJ : (elementaryAbelianMaxJ (S : Subgroup G)).map q ≠ ⊥) :
    letI : IsElementaryAbelian 2 (vSubgroup S) :=
      (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
    letI := quotientConjugationAction S q hq hker
    SectionOne.Hypotheses barG (vSubgroup S) := by
  let : IsElementaryAbelian 2 (vSubgroup S) :=
    (vSubgroup_le_twoCore_and_elementaryAbelian h S).2
  let := quotientConjugationAction S q hq hker
  let : Group.IsSolvable G := h.solvable
  let barS : Sylow 2 barG := S.mapSurjective hq
  have hJS : (elementaryAbelianMaxJ (S : Subgroup G)).map q ≤
      (barS : Subgroup barG) := by
    apply Subgroup.map_mono
    exact sSup_le fun A hA => hA.1
  have hSne : (barS : Subgroup barG) ≠ ⊥ := by
    intro hbot
    apply hJ
    exact bot_unique (hbot ▸ hJS)
  have heven : Even (Nat.card barG) := by
    have htwo : 2 ∣ Nat.card barS := by
      rcases barS.isPGroup'.card_eq_or_dvd with hone | htwo
      · exact False.elim (hSne ((Subgroup.eq_bot_iff_card _).mpr hone))
      · exact htwo
    exact even_iff_two_dvd.mpr (htwo.trans (barS : Subgroup barG).card_subgroup_dvd_card)
  exact ⟨Group.isSolvable_of_surjective hq, heven,
    quotientConjugationAction_faithful S q hq hker, lemma_two_one h S q hq hker⟩

end Stellmacher.SectionTwo
