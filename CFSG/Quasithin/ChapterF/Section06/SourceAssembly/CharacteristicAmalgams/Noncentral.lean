module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalContext
public import Stellmacher.SectionEight.LemmaEightTwo
public import Stellmacher.SectionFiveToSeven.CosetGraphConstruction
public import Stellmacher.SectionFiveToSeven.CriticalPathExistence

/-!
# Goldschmidt vertices moving the Sylow omega-center

If both characteristic-two vertices move Ω₁(Z(T)), each vertex has order
at most forty-eight. Construct the actual coset graph and a shortest critical
path. Were its endpoint centers to commute, Stellmacher (7.5) would make
the first-step center central, contrary to the specified action on Ω₁(Z(T)).
The local version of (8.2) then identifies both vertex groups as S₄ or
C₂ × S₄. All graph, quotient and local-family premises are discharged from
the original Goldschmidt triple.

This is the noncentral-omega branch of Aschbacher–Smith F.6.5(2)(vi), using
Stellmacher, Journal of Algebra 190 (1997), (7.5) and (8.2), pp.34–38.
The same local branch is Kurzweil–Stellmacher, The Theory of Finite Groups,
Theorem 10.3.11, pp.295–298. No global Hypothesis Two is required.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher Stellmacher.SectionsFiveToSeven Stellmacher.Later
open Stellmacher.SectionsFiveToSeven.CosetGraphContext
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem vertex_center_noncentral
    {S P₁ P₂ : Subgroup G} (Γ : CosetGraphContext G S P₁ P₂)
    (d : Γ.Vertex) (hs : IsSylowTwoIn S (stabilizer Γ d))
    (hmove : ⁅stabilizer Γ d, omegaOneCenter S⁆ ≠ ⊥) :
    ¬ z Γ d ≤ CenterAmbient (stabilizer Γ d) := by
  intro hz
  have hΩ : omegaOneCenter S ≤ z Γ d := by
    obtain ⟨_, T, hT⟩ := hs
    rw [z, Γ.zAt_def]
    exact le_sSup ⟨T, congrArg omegaOneCenter hT.symm⟩
  apply hmove
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact le_centralizer_iff.mp
    (hΩ.trans (hz.trans (SevenSix.centerAmbient_le_centralizer _)))

/-- Both whole vertices have the two models arising in the noncentral-omega branch. -/
theorem IsGoldschmidtTriple.local_models_of_noncentral_omega
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂)
    (hmove₁ : ⁅G₁, omegaOneCenter (G₁ ⊓ G₂)⁆ ≠ ⊥)
    (hmove₂ : ⁅G₂, omegaOneCenter (G₁ ⊓ G₂)⁆ ≠ ⊥) :
    (IsModel G₁ S4 ∨ IsModel G₁ (C2 × S4)) ∧
      (IsModel G₂ S4 ∨ IsModel G₂ (C2 × S4)) := by
  classical
  have h7 := h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂
  obtain ⟨Γ⟩ := exists_cosetGraphContext (G₁ ⊓ G₂) G₁ G₂ h.generated
  obtain ⟨cp⟩ := exists_criticalPath h7 Γ
  have hmove : ⁅stabilizer Γ cp.firstStep, omegaOneCenter (G₁ ⊓ G₂)⁆ ≠ ⊥ := by
    rcases cp.edge_stabilizers_are_P with he | he
    · rwa [he.2]
    · rwa [he.2]
  have hcenter := vertex_center_noncentral Γ cp.firstStep
    (SevenSix.edge_sylow_data h7 Γ cp).2 hmove
  have hcomm : ⁅Γ.z cp.a, Γ.z cp.a'⁆ ≠ ⊥ := by
    intro hh
    have hc := (lemma_seven_five h7 Γ cp hh).next_center.2
    apply hcenter
    rw [hc]
    exact SevenSix.omegaOneCenter_le_centerAmbient _
  let ctx : SectionEightLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
    ⟨h7, h.sixThree_local, Γ, cp, hcomm⟩
  have ha := Stellmacher.SectionEight.lemma_eight_two_local ctx hcenter cp.a
  have hb := Stellmacher.SectionEight.lemma_eight_two_local ctx hcenter cp.firstStep
  rcases cp.edge_stabilizers_are_P with he | he
  · exact ⟨by simpa only [ctx, GAt, he.1] using ha,
      by simpa only [ctx, GAt, he.2] using hb⟩
  · exact ⟨by simpa only [ctx, GAt, he.2] using hb,
      by simpa only [ctx, GAt, he.1] using ha⟩

omit [Finite G] in
private theorem card_le_forty_eight_of_models {H : Subgroup G}
    (hm : IsModel H S4 ∨ IsModel H (C2 × S4)) : Nat.card H ≤ 48 := by
  rcases hm with h | h
  · obtain ⟨e⟩ := (show Nonempty (H ≃* S4) from h)
    rw [Nat.card_congr e.toEquiv]
    norm_num [S4, Nat.card_eq_fintype_card, Fintype.card_perm]
  · obtain ⟨e⟩ := (show Nonempty (H ≃* C2 × S4) from h)
    rw [Nat.card_congr e.toEquiv]
    norm_num [C2, S4, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_perm]

/-- The actual vertex-order bound in the noncentral-omega branch. -/
theorem IsGoldschmidtTriple.local_card_le_forty_eight_of_noncentral_omega
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂)
    (hmove₁ : ⁅G₁, omegaOneCenter (G₁ ⊓ G₂)⁆ ≠ ⊥)
    (hmove₂ : ⁅G₂, omegaOneCenter (G₁ ⊓ G₂)⁆ ≠ ⊥) :
    Nat.card G₁ ≤ 48 ∧ Nat.card G₂ ≤ 48 := by
  have hm := h.local_models_of_noncentral_omega hcore hgood₁ hgood₂ hmove₁ hmove₂
  exact ⟨card_le_forty_eight_of_models hm.1, card_le_forty_eight_of_models hm.2⟩

/-- The bound for the literal vertex and overlap images in G/O₂(G). -/
theorem IsGoldschmidtTriple.quotient_card_le_forty_eight_of_noncentral_omega
    (h : IsGoldschmidtTriple G₁ G₂)
    (hgood₁ : generalizedFitting (G₁.map (QuotientGroup.mk' (pCore 2 G))) =
      pCore 2 (G₁.map (QuotientGroup.mk' (pCore 2 G))))
    (hgood₂ : generalizedFitting (G₂.map (QuotientGroup.mk' (pCore 2 G))) =
      pCore 2 (G₂.map (QuotientGroup.mk' (pCore 2 G))))
    (hmove₁ : ⁅G₁.map (QuotientGroup.mk' (pCore 2 G)),
      omegaOneCenter ((G₁ ⊓ G₂).map (QuotientGroup.mk' (pCore 2 G)))⁆ ≠ ⊥)
    (hmove₂ : ⁅G₂.map (QuotientGroup.mk' (pCore 2 G)),
      omegaOneCenter ((G₁ ⊓ G₂).map (QuotientGroup.mk' (pCore 2 G)))⁆ ≠ ⊥) :
    Nat.card (G₁.map (QuotientGroup.mk' (pCore 2 G))) ≤ 48 ∧
      Nat.card (G₂.map (QuotientGroup.mk' (pCore 2 G))) ≤ 48 := by
  rw [h.quotient_twoCore_intersection] at hmove₁ hmove₂
  exact h.quotient_twoCore.local_card_le_forty_eight_of_noncentral_omega
    h.quotient_twoCore_eq_bot hgood₁ hgood₂ hmove₁ hmove₂

end CFSG.Quasithin.ChapterF
