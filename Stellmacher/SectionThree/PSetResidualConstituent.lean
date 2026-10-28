module

public import Stellmacher.SectionThree.ResidualActiveChiefSection
public import Theory.GroupAction.SubquotientConjugationFixedBound

/-!
# A residual-nontrivial irreducible binary constituent

A nontrivial residual action on an elementary abelian two-subgroup has an
actual invariant irreducible section on which the residual still acts
nontrivially. The chief-section extraction uses the proved two-layer kernel
lemma, not semisimplicity. The original common fixed index descends through
the section to the whole actor image on its literal quotient.

This supplies the constituent used in the fixed-hyperplane step of
Stellmacher (8.4), printed p.40/PDF p.30. No local PSet or solvability
hypotheses are needed for this extraction.
-/

namespace Stellmacher.SectionThree

public theorem exists_residual_nontrivial_irreducible_constituent
    {H : Type*} [Group H] [Finite H] (P C A : Subgroup H)
    (hCP : C ≤ P) (hCN : (C.subgroupOf P).Normal)
    (hC : IsElementaryAbelian 2 C) (_hAP : A ≤ P) (_hA : IsElementaryAbelian 2 A)
    (hres : ⁅twoResidualAmbient P,C⁆ ≠ ⊥)
    (hfixed : Nat.card C =
      2 * Nat.card (C ⊓ Subgroup.centralizer (A : Set H) : Subgroup H)) :
    ∃ E D : Subgroup H, ∃ _hEC : E ≤ C, ∃ _hDE : D ≤ E,
      ∃ _hEN : (E.subgroupOf P).Normal, ∃ _hDN : (D.subgroupOf P).Normal,
      ∃ hPE : P ≤ Subgroup.normalizer (E : Set H),
      ∃ _hPD : P ≤ Subgroup.normalizer (D : Set H),
      ∃ hN : (D.subgroupOf E).Normal,
      let _ := hN
      ∃ action : P →* MulAut (E ⧸ D.subgroupOf E),
        (∀ actor : P, ∀ value : E,
          action actor (QuotientGroup.mk' (D.subgroupOf E) value) =
            QuotientGroup.mk' (D.subgroupOf E)
              ⟨(actor : H) * (value : H) * (actor : H)⁻¹,
                (Subgroup.mem_normalizer_iff.mp (hPE actor.property) value).mp value.property⟩) ∧
        IsElementaryAbelian 2 (E ⧸ D.subgroupOf E) ∧
        (∀ K : Subgroup (E ⧸ D.subgroupOf E),
          (∀ actor : P, ∀ value, value ∈ K → action actor value ∈ K) → K = ⊥ ∨ K = ⊤) ∧
        (¬twoResidualSubgroup P ≤ action.ker) ∧
        Nat.card (E ⧸ D.subgroupOf E) ≤
          2 * Nat.card (FixedPoints.subgroup ((A.subgroupOf P).map action)
            (E ⧸ D.subgroupOf E)) := by
  obtain ⟨E, D, hEC, hDE, hPE, hPD, hN, action, haction, hW, hirr, hescape⟩ :=
    exists_residual_active_chief_section P C hCP hCN hC hres
  let _ := hN
  have hEN : (E.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hEC.trans hCP)).mpr hPE
  have hDN : (D.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hDE.trans (hEC.trans hCP))).mpr hPD
  exact ⟨E, D, hEC, hDE, hEN, hDN, hPE, hPD, hN, action, haction, hW, hirr, hescape,
    Subgroup.subquotient_conjugation_actor_fixed_card_bound P C E D A hEC hPE hN
      action haction 2 hfixed.le⟩

end Stellmacher.SectionThree
