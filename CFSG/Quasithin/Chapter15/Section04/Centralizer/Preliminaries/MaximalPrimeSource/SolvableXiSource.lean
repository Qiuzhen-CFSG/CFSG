module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.SourceInputs
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.SolvableOvergroup
public import CFSG.Quasithin.Chapter3.Section02.SourceXiSigns
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Subnormal
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# The original uppercase Ξ clause from solvable maximal two-locals

The proved solvable embedding theorem gives the exact normalizer uniqueness
for every actual Ξ member. Two different maximal two-local overgroups of the
original omega-center centralizer then force noncentrality. Characteristic
two puts that omega-center inside the omega-center of O₂(XT); the proved
A.4.8 module comparison gives genuine faithful Ξ membership.

The preceding empty-local and solvability clauses, and the literal earlier
3.2.13 inclusion, assemble all of 15.4.2(1–3). In particular the five-case
restriction remains on the actual normalizer-induced automizer of X/O₂(X).
The earlier clauses and 3.2.13 are supplied by the prime-reduction and Chapter
3 owners. No general Chapter 1.3 classification premise is retained.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.4.2(3),
printed p.1156, using 1.3.7, A.4.8 and Definition 3.2.12/Lemma 3.2.13.
-/

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
open ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem faithful_of_xi_noncentral
    (T : Sylow 2 G) (h : SourceHypotheses T) {X : Subgroup G}
    (hX : X ∈ Chapter1.Xi G (T : Subgroup G))
    (hnoncentral : ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), X⁆ ≠ ⊥) :
    IsFaithfulSignalizerType X := by
  let H := X ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  have hXH : X ≤ H := le_sup_left
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have h114 := Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
  have hHe : H ∈ Chapter1.He G := h114 ⟨hX.join_mem_H, hTH⟩
  have hXe : X ∈ Chapter1.He G := hX.mem_He
    (fun _ hM _ hN hNM hn => Chapter1.lemma_1_1_3_1 hM hN hNM hn) h114
  have hsignalizer : IsSignalizerType X :=
    ⟨hX.ne_bot, hX.perfect,
      generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp hXe)⟩
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hZQ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤
      Stellmacher.omegaOneCenterAmbient Q := by
    intro z hz
    obtain ⟨hzT, hzpow, hzcentral⟩ :=
      (Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
    have hzC : z ∈ centralizer (Q : Set G) := by
      apply mem_centralizer_iff.mpr
      intro q hq
      exact hzcentral q (hQT hq)
    have hzQ : z ∈ Q := hHe ⟨hTH hzT, hzC⟩
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff Q z).mpr
      ⟨hzQ, hzpow, fun q hq => hzcentral q (hQT hq)⟩
  have hXQ : X ≤ normalizer Q := hXH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_intrinsicCore H))
  have hsub : (X.subgroupOf H).IsSubnormal := hX.normal_in_join.isSubnormal
  have hcore : X.pCoreIn 2 ≤ Q := pCoreAmbient_mono_of_isSubnormalIn X H 2 hXH hsub
  have hsig : IsTwoSignalizer X H Q :=
    (isTwoSignalizer_iff X H Q).mpr ⟨pCoreIn_le 2 H, isPGroup_pCoreIn 2 H, hXQ⟩
  have hcomm : ⁅X, Q⁆ ≤ X.pCoreIn 2 :=
    signalizer_commutator_le_pCore X H Q hXH hsub hX.perfect hsig
  have hmodule : signalizerModule X Q ≠ ⊥ := by
    intro hb
    apply hnoncentral
    apply bot_unique
    have hc := commutator_mono hZQ (le_rfl : X ≤ X)
    rw [commutator_comm (Stellmacher.omegaOneCenterAmbient Q) X,
      ← signalizerModule_eq_commutator_omegaCenter X Q, hb] at hc
    exact hc
  exact ⟨hsignalizer, (signalizerModule_ne_bot_iff_intrinsic X Q hX.perfect
    (isPGroup_pCoreIn 2 H) hXQ hcore hcomm).mp hmodule⟩

omit [Finite G] in
private theorem quotient_three_or_five_of_negative
    {T X : Subgroup G} (hX : X ∈ Chapter1.Xi G T) (hminus : X ∈ XiMinus T) :
    IsPGroup 3 (Chapter1.XiQuotient X) ∨ IsPGroup 5 (Chapter1.XiQuotient X) := by
  rcases hminus.2 with h23 | ⟨h5, _⟩
  · obtain ⟨p, hp, ho, hq⟩ := hX.odd_quotient
    let : Fact p.Prime := ⟨hp⟩
    have hdq : p ∣ Nat.card (Chapter1.XiQuotient X) :=
      hq.isPGroup.card_eq_or_dvd.resolve_left (by
        intro hone
        have hh := hq.one_lt_card hp
        omega)
    have hdx : p ∣ Nat.card X := hdq.trans (card_quotient_dvd_card (pCore 2 X))
    rcases h23 p hp hdx with hp2 | hp3
    · subst p
      norm_num at ho
    · subst p
      exact Or.inl hq.isPGroup
  · exact Or.inr h5

/-- Original 15.4.2(3), using the preceding clauses (1),(2) separately and
preserving the literal source 3.2.13 automizer restriction. -/
public theorem source_lemma_15_4_2_three_of_solvable
    (T : Sylow 2 G) (h : SourceHypotheses T)
    (hLocal : Chapter1.L G (T : Subgroup G) = ∅)
    (hsol : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      (T : Subgroup G) ≤ M → Group.IsSolvable M)
    (h3213 : Chapter1.XiStarF G (T : Subgroup G) ⊆
      Chapter3.XiMinus G (T : Subgroup G))
    {X : Subgroup G} (hX : X ∈ Chapter1.Xi G (T : Subgroup G)) :
    ⁅Stellmacher.omegaOneCenterAmbient (T : Subgroup G), X⁆ ≠ ⊥ ∧
      X ∈ Chapter1.XiStarF G (T : Subgroup G) ∧ X ∉ XiPlus (T : Subgroup G) ∧
      (IsPGroup 3 (Chapter1.XiQuotient X) ∨ IsPGroup 5 (Chapter1.XiQuotient X)) := by
  have huniq := (Chapter1.XiEmbedding.normalizer_unique_of_solvable_maximalTwoLocals
    h.simpleQTKE T hsol hX).2
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  have hnoncentral : ⁅Z, X⁆ ≠ ⊥ := by
    intro hc
    have hXZ : X ≤ centralizer (Z : Set G) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      rwa [commutator_comm]
    have hTZ : (T : Subgroup G) ≤ centralizer (Z : Set G) := by
      intro t ht
      apply mem_centralizer_iff.mpr
      intro z hz
      exact ((Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz).2.2 t ht |>.symm
    obtain ⟨M₁, M₂, hM₁, hM₂, hC₁, hC₂, hne⟩ := h.centralizer_overgroups
    have h₁ : M₁ = normalizer (X : Set G) := by
      apply Set.mem_singleton_iff.mp
      rw [← huniq]
      exact ⟨hM₁, (sup_le hXZ hTZ).trans hC₁⟩
    have h₂ : M₂ = normalizer (X : Set G) := by
      apply Set.mem_singleton_iff.mp
      rw [← huniq]
      exact ⟨hM₂, (sup_le hXZ hTZ).trans hC₂⟩
    exact hne (h₁.trans h₂.symm)
  have hstar : X ∈ Chapter1.XiStar G (T : Subgroup G) := by
    refine ⟨hX, ?_⟩
    intro L hL
    rw [hLocal] at hL
    exact hL.elim
  have hstarf : X ∈ Chapter1.XiStarF G (T : Subgroup G) :=
    ⟨⟨hX, faithful_of_xi_noncentral T h hX hnoncentral⟩, hstar⟩
  have hminus : X ∈ XiMinus (T : Subgroup G) := h3213 hstarf
  exact ⟨hnoncentral, hstarf, fun hplus => hplus.2 hminus,
    quotient_three_or_five_of_negative hX hminus⟩

/-- Actual assembly of the full earlier 15.4.2(1–3) record. The genuine
preceding clauses and 3.2.13 remain explicit for their source owners. -/
public theorem source_earlier1542Conclusion_of_solvable
    (T : Sylow 2 G) (h : SourceHypotheses T)
    (hLocal : Chapter1.L G (T : Subgroup G) = ∅)
    (hsol : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      (T : Subgroup G) ≤ M → Group.IsSolvable M)
    (h3213 : Chapter1.XiStarF G (T : Subgroup G) ⊆
      Chapter3.XiMinus G (T : Subgroup G)) :
    Earlier1542Conclusion T :=
  ⟨hLocal, hsol, fun _ hX => source_lemma_15_4_2_three_of_solvable T h hLocal hsol h3213 hX⟩

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
