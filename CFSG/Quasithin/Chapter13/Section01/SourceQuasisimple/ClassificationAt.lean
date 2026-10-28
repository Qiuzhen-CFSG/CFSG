module

public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.AlternatingSevenInputAt
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Refinement.Source
public import Theory.Alternating.OddCentralCovers
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!+# The five quasisimple quotients at the original G,T

Apply the seven-module theorem to an actual chosen module. The alternating
actors are quotients by C_L(V), so first recover the central quotient of
L/O₂(L). Its odd center and the alternating covering theorem retain the
triple cover of A₆. The guarded 12.3.1 theorem excludes A₇; the separate
12.9.1 input excludes binary L₄ and L₅, including the A₈ presentation.
The resulting literal five-model list gives comparable-local rigidity.

The structural and module inputs belong to qt-d-1222-source and
qt-d-1222-modules (with normalization supplied by qt-d-1222-normalization).
The only further premise is the exact larger-linear exclusion owned by
qt-d-1291-source. Final discharge of these inputs remains with qt-d-1317-source.
Source: Aschbacher--Smith, 12.2.2, 12.3.1, 12.9.1 and 13.1.2(3,5),
printed pp.795,807--812,857--866.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01.SourceQuasisimple
open Chapter1 Chapter12.Section02 Chapter12.Section03.SourceAlternatingSeven
open SourceNonquasisimple.Supplements.Escape
open Chapter13.Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The source's G₂(2)′ and U₃(3) names denote the same actual group;
the triple cover retains the full center, not just its simple quotient. -/
theorem FiveQuotients.midSize {Q : Type*} [Group Q] [Finite Q]
    (h : FiveQuotients Q) : MidSizeModel Q := by
  rcases h with h5 | h3 | h6 | ⟨hq,hc,eq⟩ | hg
  · exact Or.inl h5
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr (Or.inl h6))
  · have hz := (zmodCyclicMulEquiv (isCyclic_of_prime_card hc)).symm
    rw [hc] at hz
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hq,⟨hz⟩,eq⟩)))
  · obtain ⟨eg⟩ := hg
    obtain ⟨b⟩ := Atlas.G2.nonempty_commutator_binary_equiv_psu3
    apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
    refine ⟨GaloisField 3 2,inferInstance,inferInstance,ABG.unitaryForm 3 3 1 (by decide),
      GaloisField.card 3 2 (by decide),?_,⟨eg.trans b⟩⟩
    intro x
    change iterateFrobeniusEquiv (GaloisField 3 2) 3 1 x = x ^ 3
    simp only [iterateFrobeniusEquiv_def,pow_one]

private theorem binary_linear {Q : Type*} [Group Q] {n : ℕ} (hn : 0 < n)
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    ClassicalGroup.IsPSL Q n 2 := by
  exact ⟨ZMod 2,inferInstance,inferInstance,by simp,
    ⟨e.trans ((BinaryLinear.OuterCyclic.slEquivLinear n).trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear hn).symm)⟩⟩

private def alternating_central_quotient {L V : Subgroup G}
    (hq : IsQuasisimple (XiQuotient L)) (D : ChosenModule T L V)
    {n : ℕ} (hn : 4 ≤ n)
    (e : letI := D.actionCentralizer_normal;
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin n)) :
    (XiQuotient L ⧸ center (XiQuotient L)) ≃* alternatingGroup (Fin n) := by
  let := hq
  let := D.actionCentralizer_normal
  let : Nontrivial (alternatingGroup (Fin n)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simpa using (show 3 ≤ n by omega))
  let f := e.toMonoidHom.comp D.coreToFaithful
  exact (IsQuasisimple.centralQuotientEquiv f
    (e.surjective.comp D.coreToFaithful_surjective)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simpa using hn))).trans
        QuotientGroup.quotientBot)

/-- The seven-module list gives the literal five quotient models, with
only the independently owned 12.9.1 exclusion retained. -/
theorem fiveQuotients_of_source_inputs_at
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (larger : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL (XiQuotient I) n 2)
    {L : Subgroup G} (hi : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    FiveQuotients (XiQuotient L) := by
  let := hi.quasisimple
  obtain ⟨V,⟨D⟩⟩ := (structural L hi).2.1
  let := D.actionCentralizer_normal
  have hseven : ¬ Nonempty ((XiQuotient L ⧸ center (XiQuotient L)) ≃*
      alternatingGroup (Fin 7)) := by
    rintro ⟨e⟩
    exact Chapter13.Section03.SourceClassification.alternatingSeven_excluded_of_source_inputs_at
      h hi hmany structural modules ⟨(centralPreimageQuotientEquiv (pCore 2 L)).trans e⟩
  have halt {n : ℕ} (hlo : 5 ≤ n) (hhi : n ≤ 8)
      (e : letI := D.actionCentralizer_normal;
        (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin n)) :
      FiveQuotients (XiQuotient L) := by
    let a := alternating_central_quotient hi.quasisimple D (by omega) e
    have ho : Odd (Nat.card (center (XiQuotient L))) := by
      apply Nat.not_even_iff_odd.mp
      rw [even_iff_two_dvd]
      exact PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
        (pCore_quotient_pCore_eq_bot 2) _ le_rfl
    have hne7 : n ≠ 7 := by
      rintro rfl
      exact hseven ⟨a⟩
    rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives n hlo a ho with hc | ⟨hn,hc⟩
    · let b := GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne n a hc
      have hn : n = 5 ∨ n = 6 ∨ n = 8 := by omega
      rcases hn with rfl | rfl | rfl
      · exact Or.inl ⟨b⟩
      · exact Or.inr (Or.inr (Or.inl ⟨b⟩))
      · exact (larger L hi 4 (Or.inl rfl)
          ⟨ZMod 2,inferInstance,inferInstance,by simp,
            ⟨b.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩).elim
    · have hn6 : n = 6 := hn.resolve_right hne7
      subst n
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hi.quasisimple,hc,⟨a⟩⟩)))
  cases modules L V hi D with
  | linear n hn a =>
    rcases hn with rfl | rfl | rfl
    · exact Or.inr (Or.inl (binary_linear (by decide) a.groupEquiv))
    · exact (larger L hi 4 (Or.inl rfl) (binary_linear (by decide) a.groupEquiv)).elim
    · exact (larger L hi 5 (Or.inr rfl) (binary_linear (by decide) a.groupEquiv)).elim
  | linearThreeExtension e _ _ =>
    exact Or.inr (Or.inl (binary_linear (by decide) e))
  | linearFiveExterior e _ _ =>
    exact (larger L hi 5 (Or.inr rfl) (binary_linear (by decide) e)).elim
  | alternating n hlo hhi a => exact halt hlo hhi a.groupEquiv
  | alternatingSevenFour e _ =>
    exact (hseven ⟨alternating_central_quotient hi.quasisimple D (by decide) e⟩).elim
  | g2 a => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a.groupEquiv⟩)))
  | tripleSix e _ _ _ =>
    have hc : Nat.card (center (XiQuotient L)) = 3 :=
      (Nat.card_congr (centerCongr e).toEquiv).trans Representation.Hexacode.even_center_card
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hi.quasisimple,hc,
      ⟨(QuotientGroup.congr _ _ e (map_center_equiv e)).trans
        Representation.Hexacode.even_quotient_center_equiv⟩⟩)))

/-- Construct both exact earlier-source premises consumed by the supplement
and escaping-subgroup arguments, at the same ambient G,T. -/
theorem quasisimple_sources_of_inputs_at
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (larger : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL (XiQuotient I) n 2) :
    QuasisimpleRigidity T ∧ QuasisimpleClassification T := by
  have models (I : Subgroup G) (hi : Hypothesis1223 KnownSimple.IsKnownSimple T I) :=
    fiveQuotients_of_source_inputs_at h hmany structural modules larger hi
  refine ⟨?_,fun I hf hq => models I (h.hypothesis1223 hf hq)⟩
  intro I hf hq
  have hi := h.hypothesis1223 hf hq
  refine ⟨(structural I hi).1,?_⟩
  intro B hB hBI
  exact local_eq_of_midSize hf.1.1 hB hBI (FiveQuotients.midSize (models I hi))

end CFSG.Quasithin.Chapter13.Section01.SourceQuasisimple
