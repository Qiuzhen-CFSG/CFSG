module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.Preparation
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple

/-!
# Original 1.1.5 data on the ordinary escaping component

Choose an involution in Z(T). The original uniqueness control puts its
centralizer in M = N_G(L). Together with the full Sylow subgroup of C_G(u),
this satisfies every hypothesis of 1.1.6 and hence supplies the genuine
1.1.5 component model and its conjugation action. The same z, K, T and M
are retained throughout. This is the catalogue input to the ordinary
central-cover comparison, not that comparison itself.

Source: Aschbacher–Smith, 1.1.5–6, pp.501–503; 13.1.12(3), p.875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The original central Sylow involution supplies the full marked ordinary catalogue. -/
theorem Context.ordinary_model_action (h : Context T L p) (c : Control T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hq : IsQuasisimple K) :
    ∃ (S : Sylow 2 (centralizer ({u} : Set G))) (z : G),
      (S : Subgroup (centralizer ({u} : Set G))).map
        (centralizer ({u} : Set G)).subtype = (T : Subgroup G) ⊓ centralizer ({u} : Set G) ∧
      orderOf z = 2 ∧ z ∈ (T : Subgroup G) ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      Lemma115Hypotheses (centralizer ({u} : Set G)) S (normalizer (L : Set G)) z ∧
      K = ⁅K,zpowers z⁆ ∧ ¬ K ≤ normalizer (L : Set G) ∧
      HasModelAction115 (K.subgroupOf (centralizer ({u} : Set G))) z := by
  let H := centralizer ({u} : Set G)
  let B := zpowers u
  have hu := h.involution s.mem s.ne_one
  obtain ⟨S,hS⟩ := e.full_sylow
  obtain ⟨z,hz,hzT,hTz⟩ := h.exists_central_involution
  have hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G) := hS ▸ inf_le_left
  have hBne : B ≠ ⊥ := zpowers_ne_bot.mpr (by intro he; simp [he] at hu)
  have hB : IsPGroup 2 B := IsPGroup.of_card (n := 1) (by
    simpa only [B,Nat.card_zpowers,pow_one] using hu)
  have hBH : B ≤ H := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCH : centralizer (B : Set G) = H := by
    change centralizer (zpowers u : Set G) = centralizer ({u} : Set G)
    rw [zpowers_eq_closure,centralizer_closure]
  have hHN : H ≤ normalizer (B : Set G) := hCH ▸ Subgroup.centralizer_le_normalizer _
  have hmax := (RadicalConjugateRigidity.maximal_radical_structure h.hypothesis.simpleQTKE
    T h.maximal.1 h.nonquasisimple h.odd h.divides).2.2
  have h115 : Lemma115Hypotheses H S (normalizer (L : Set G)) z :=
    lemma_1_1_6 hBne hB hBH hCH.le hHN S T hST hz hzT
      (fun t ht => mem_centralizer_singleton_iff.mp (hTz ht)) hmax
      (h.central_involution_control_of_unique c.unique_overgroup z hz hTz)
      (fun N hN hTN => mem_He_iff.mpr (h.hypothesis.simpleQTKE.evenCharacteristic T N hN hTN))
  have hD : IsComponent H (K.subgroupOf H) :=
    ⟨e.component.2.subnormal,hq.of_mulEquiv (subgroupOfEquivOfLe e.component.1).symm⟩
  obtain ⟨hcomm,hout,hmodel⟩ := lemma_1_1_5_three_knownSimple h.hypothesis.simpleQTKE
    H S (normalizer (L : Set G)) z h115 (K.subgroupOf H) hD
  rw [map_subgroupOf_eq_of_le e.component.1] at hcomm hout
  exact ⟨S,z,hS,hz,hzT,hTz,h115,hcomm,hout,hmodel⟩

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
