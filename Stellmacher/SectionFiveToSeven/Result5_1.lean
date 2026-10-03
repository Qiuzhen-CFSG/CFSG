module
public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.SectionFiveToSeven.FiveOneUniqueBranch
public import Stellmacher.SectionFour.LemmaFourSeven

/-!
# Stellmacher (5.1): the initial pair under Hypothesis One

Under Hypothesis One there is a nontrivial subgroup S of the fixed Sylow
S0 and a pair P1,P2 in its local family with trivial two-core of their
join, satisfying exactly the alternatives recorded by FiveOneConditions.
The universal Sylow clause and stability conditions in alternative (c)
remain unchanged.

The finite subgroup lattice supplies a maximal two-local subgroup over S0.
If it is unique, the imported consecutive-maxima construction gives the
source's alternative (c). Otherwise the two distinct maxima supply the
Section Four hypotheses, and (4.7) gives a critical pair with its first
member outside C and second member in pZero. Convert the exact local-family
notation to Section Five. A starred second member over C gives alternative
(b). Otherwise both members lie outside C, and the proved omega-normality
centralizer criterion gives alternative (a).

Source: refs/latex/stellmacher-n-group.tex, statement and proof (5.1),
Journal of Algebra 190 (1997), journal pp27-28. This assembles the unique
branch with the first-paragraph reduction to (4.7).
-/

namespace Stellmacher.SectionsFiveToSeven
universe u
variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
private theorem isLMember_iff_lSet (U S P : Subgroup H) :
    IsLMember U S P ↔ P ∈ SectionThree.LSet U S := by
  constructor
  · rintro ⟨hPU, hSyl, hQ, hneq⟩
    exact ⟨hPU, hSyl.2, hQ, hneq⟩
  · rintro ⟨hPU, hSyl, hQ, hneq⟩
    have hSP : S ≤ P := by
      obtain ⟨T, hT⟩ := hSyl
      rw [← hT]
      exact Subgroup.map_subtype_le _
    exact ⟨hPU, ⟨hSP, hSyl⟩, hQ, hneq⟩

omit [Finite H] in
private theorem pStarFamily_of_pStarSet (U S P : Subgroup H)
    (hP : P ∈ SectionThree.PStarSet U S) : P ∈ PStarFamily U S := by
  obtain ⟨hP, L, hL, hsub⟩ := hP
  refine ⟨(pFamily_iff_pSet U S P).mpr hP, L, ?_, hsub⟩
  refine ⟨(isLMember_iff_lSet U S L).mpr hL.1, ?_⟩
  intro L' hL' hLL'
  exact hL.2 L' ((isLMember_iff_lSet U S L').mp hL') hLL'

private theorem distinct_branch
    (S0 : Sylow 2 H) (h : HypothesisOne H S0)
    (M1 M2 : Subgroup H) (hne : M1 ≠ M2)
    (hM1 : IsMaximalTwoLocalContaining (S0 : Subgroup H) M1)
    (hM2 : IsMaximalTwoLocalContaining (S0 : Subgroup H) M2) :
    ∃ S P1 P2 : Subgroup H, FiveOneConditions H S0 S P1 P2 := by
  have h4 : SectionFour.Hypotheses H S0 :=
    ⟨h.even_order, h.local_solvable_characteristicTwo,
      M1, M2, hne, hM1.1, hM2.1, hM1.2, hM2.2⟩
  obtain ⟨P, Pstar, hLambda, hPnotC, hPstar0⟩ := SectionFour.lemma_four_seven S0 h4
  have hP := (pFamily_iff_pSet (⊤ : Subgroup H) (S0 : Subgroup H) P).mpr hLambda.1
  have hPstar := (pFamily_iff_pSet (⊤ : Subgroup H) (S0 : Subgroup H) Pstar).mpr hLambda.2.1
  have hjoin : twoCoreIn (P ⊔ Pstar) = ⊥ := hLambda.2.2
  have hS0ne : (S0 : Subgroup H) ≠ ⊥ := S0.ne_bot_of_dvd_card h.even_order.two_dvd
  rcases hPstar0 with hPstarC | hPstarOutside
  · exact ⟨S0, P, Pstar, hS0ne, le_rfl, hP, hPstar, hjoin,
      FiveOneAlternative.b rfl (pStarFamily_of_pStarSet _ _ _ hPstarC)⟩
  · have hPstarNotC : ¬ Pstar ≤ SectionFour.cSubgroup S0 := by
      intro hle
      apply hPstarOutside.2
      exact ⟨⟨hle, hPstarOutside.1.1.1.2⟩, hPstarOutside.1.1.2⟩
    have hPnotNormal : ¬ NormalIn (omegaOneCenter (S0 : Subgroup H)) P := by
      intro hnorm
      exact hPnotC (normalInOmega_imp_le_centralizer _ _ hP hnorm)
    have hPstarNotNormal : ¬ NormalIn (omegaOneCenter (S0 : Subgroup H)) Pstar := by
      intro hnorm
      exact hPstarNotC (normalInOmega_imp_le_centralizer _ _ hPstar hnorm)
    exact ⟨S0, P, Pstar, hS0ne, le_rfl, hP, hPstar, hjoin,
      FiveOneAlternative.a rfl hPnotNormal hPstarNotNormal⟩

/-- Stellmacher (5.1), with the full source alternatives. -/
public theorem lemma_five_one
    (S0 : Sylow 2 H) (h : HypothesisOne H S0) :
    ∃ S P1 P2 : Subgroup H, FiveOneConditions H S0 S P1 P2 := by
  classical
  have hS0ne : (S0 : Subgroup H) ≠ ⊥ := S0.ne_bot_of_dvd_card h.even_order.two_dvd
  have hlocal : IsTwoLocal (Subgroup.normalizer (S0 : Set H)) :=
    ⟨(S0 : Subgroup H), hS0ne, S0.isPGroup', rfl⟩
  obtain ⟨M, hNM, hMmax⟩ := Finite.exists_le_maximal hlocal
  have hM : IsMaximalTwoLocalContaining (S0 : Subgroup H) M :=
    ⟨hMmax, Subgroup.le_normalizer.trans hNM⟩
  by_cases huniq : ∀ M' : Subgroup H,
      IsMaximalTwoLocalContaining (S0 : Subgroup H) M' → M' = M
  · exact five_one_unique_branch S0 h M ⟨hM, huniq⟩
  · push Not at huniq
    obtain ⟨M', hM', hne⟩ := huniq
    exact distinct_branch S0 h M M' (Ne.symm hne) hM hM'

end Stellmacher.SectionsFiveToSeven
