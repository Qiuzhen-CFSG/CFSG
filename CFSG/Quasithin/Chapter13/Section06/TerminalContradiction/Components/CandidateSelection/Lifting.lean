module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LiftingSieve
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LiftingModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.EmbeddingNormality
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
/-!
# Lifting the actual exceptional seed to the containing component

Apply the genuine A.3.12 theorem in the ambient two-core quotient. The
exceptional section sieve gives equality of the two images or a containing
M₂₃ image. In the equality case, local C-component maximality lifts equality
before quotienting. In the other case the normal containing component has
intrinsic quotient M₂₃ and is itself an adequate terminal candidate.

Thus the terminal argument does not need the stronger assertion that the
original L₃(4) seed cannot enlarge to M₂₃. Its possible enlargement already
belongs to the exact terminal list. The original Sylow invariance supplies
normality through the proved component-orbit bound.

Source: Aschbacher–Smith 13.6.27, p.934, and 1.2.4, p.505.
-/
@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
open Chapter1 Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {H : Type u} [Group H] [Finite H]

private def imageCoreEquiv (B : Subgroup H) :
    (B ⧸ pCore 2 B) ≃* ((B.map (QuotientGroup.mk' (pCore 2 H))) ⧸
      pCore 2 (B.map (QuotientGroup.mk' (pCore 2 H)))) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  apply MonoidHom.quotientPCoreEquivOfSurjective (q.subgroupMap B) (q.subgroupMap_surjective B)
  rw [ker_subgroupMap, QuotientGroup.ker_mk']
  exact pCore_isPGroup.comap_subtype

omit [Finite H] in
private theorem eq_of_local_image_eq (S : Sylow 2 H) {B K : Subgroup H}
    (hB : B ∈ L H S) (hK : K.IsCComponent) (hBK : B ≤ K)
    (he : B.map (QuotientGroup.mk' (pCore 2 H)) =
      K.map (QuotientGroup.mk' (pCore 2 H))) : B = K := by
  have hKB : K ≤ B ⊔ pCore 2 H := by
    have hh := map_le_iff_le_comap.mp he.ge
    simpa only [comap_map_eq, QuotientGroup.ker_mk'] using hh
  have hKS : K ≤ B ⊔ S := hKB.trans
    (sup_le_sup_left (pCore_isPGroup.le_sylow_of_normal S) B)
  have hh := hB.1.eq_of_le (hK.subgroupOf hKS) (comap_mono hBK)
  have hm := congrArg (map (B ⊔ S).subtype) hh
  rwa [map_subgroupOf_eq_of_le le_sup_left, map_subgroupOf_eq_of_le hKS] at hm

/-- A Sylow-invariant local exceptional seed produces an actual normal
exceptional C-component in its larger ambient local group. The original
A.3.12 premise is retained in its full source form. -/
theorem exists_normal_candidate_of_local_candidate {κ : GroupClass.{u}}
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ (S : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (hQ : IsSQTK κ (H ⧸ pCore 2 H))
    (S : Sylow 2 H) {B : Subgroup H} (hB : B ∈ L H S)
    (hn : (S : Subgroup H) ≤ normalizer (B : Set H))
    (hc : Candidate (S : Subgroup H) B) :
    ∃ K : Subgroup H, K.IsCComponent ∧ K.Normal ∧ B ≤ K ∧ Candidate (S : Subgroup H) K := by
  obtain ⟨K, hK, hBK, _, hemb, hnormal⟩ := lemma_1_2_4_of_A_3_12 hA312 hQ S hB
  let : K.Normal := hnormal hn
  obtain ⟨⟨m, hm, hcard⟩, hbinary⟩ := candidate_sieve_inputs hc
  let q := QuotientGroup.mk' (pCore 2 H)
  let e := imageCoreEquiv B
  have hcard' : Nat.card ((B.map q) ⧸ pCore 2 (B.map q)) = m :=
    (Nat.card_congr e.toEquiv).symm.trans hcard
  have hbinary' : ¬ ClassicalGroup.IsPSL ((B.map q) ⧸ pCore 2 (B.map q)) 4 2 := by
    rintro ⟨F, _, _, hF, ⟨j⟩⟩
    exact hbinary ⟨F, inferInstance, inferInstance, hF, ⟨e.trans j⟩⟩
  rcases lifting_alternatives_of_section_order (map_mono hBK) hm hcard' hbinary' hemb
      with heq | hM
  · have heq := eq_of_local_image_eq S hB hK hBK heq
    exact ⟨K, hK, inferInstance, hBK, heq ▸ hc⟩
  · obtain ⟨j⟩ := hM
    exact ⟨K, hK, inferInstance, hBK,
      Or.inr (Or.inl ⟨(coreQuotientEquivImage 2 K).trans j⟩)⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
