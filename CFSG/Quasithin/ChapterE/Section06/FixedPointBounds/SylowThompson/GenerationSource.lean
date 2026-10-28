module
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Embedding
public import CFSG.Quasithin.ChapterE.Section05.SourceGeneration
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson.Transport
public import Stellmacher.OmegaOneCenterMap
/-!
# E.6.26 from the actual E-generation witness

The source higher-Thompson hypothesis identifies J(S) with J(Q). Uniqueness
of the maximal two-local containing N(Q) then controls N(J(S)). The same
hypothesis places V in the omega-center of J_j(S). Each small-codimension
subspace of this center meets V in codimension at most j, so its centralizer
lies in N(V). The proved E.5.2 generation theorem now gives H ≤ M.

The theorem takes genuine E-generation on H. Its numerical corollary uses
positive attained n(H); it does not replace the still broader arbitrary
finite-group attainment assertion. Every Sylow and center subgroup is
transported through the actual subgroup embedding.
Source: Aschbacher–Smith E.6.26, printed p.256.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson
open ChapterB
universe u
variable {G : Type u} [Group G] [Finite G]

theorem normalizer_thompson_le_of_control {κ : GroupClass.{u}} {T : Sylow 2 G}
    {M V A : Subgroup G} (h : HypothesisE61 κ T M V) {j : ℕ}
    (hj : (j : ℕ∞) < globalR V)
    (hQA : sylowCentralizer (T : Subgroup G) V ≤ A) (hAT : A ≤ T)
    (hJ : thompsonJ A j ≤ centralizer (V : Set G)) :
    normalizer (thompsonJ A 0 : Set G) ≤ M := by
  let Q := sylowCentralizer (T : Subgroup G) V
  have hr : j < twoRank A := rank_bound h (h.le_sylowCentralizer.trans hQA) hj
  have hJQ : thompsonJ A 0 ≤ Q :=
    le_inf ((thompsonJ_le A 0).trans hAT)
      ((lemma_B_2_3_1 A (Nat.zero_le j) hr).trans hJ)
  have hJ0 : thompsonJ A 0 = thompsonJ Q 0 :=
    lemma_B_2_3_3 A Q (Nat.zero_le j |>.trans_lt hr) hJQ hQA
  have hne : thompsonJ Q 0 ≠ ⊥ := by
    intro hz
    obtain ⟨B,hB⟩ := elementaryAbelianMaxSubgroups_nonempty A
    have hBJ : B ≤ thompsonJ A 0 := by rw [thompsonJ_zero]; exact le_sSup hB
    have hBb : B = ⊥ := le_bot_iff.mp (hJ0 ▸ hBJ |>.trans hz.le)
    have hc := card_eq_elementaryAbelianMaxOrder A B hB
    rw [hBb] at hc
    have hm : elementaryAbelianMaxOrder A = 1 := by simpa using hc.symm
    have hzR : twoRank A = 0 := by simp [twoRank,hm]
    omega
  rw [hJ0]
  exact normalizer_le_of_unique_maximalTwoLocal h.unique
    (T.isPGroup'.to_le ((thompsonJ_le Q 0).trans inf_le_left)) hne
    (inf_le_right.trans (normalizer_le_normalizer_thompson Q 0))

theorem source_E_6_26_of_isEGenerated
    {κ : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 κ T M V) {j : ℕ} (hjpos : 0 < j)
    (H : Subgroup G) (S : Sylow 2 H) (hgen : IsEGenerated j H)
    (hQA : sylowCentralizer (T : Subgroup G) V ≤ (S : Subgroup H).map H.subtype)
    (hAT : (S : Subgroup H).map H.subtype ≤ T)
    (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ ((S : Subgroup H).map H.subtype) j ≤ centralizer (V : Set G)) :
    H ≤ M ∧ normalizer ((S : Subgroup H).map H.subtype : Set G) ≤ M := by
  let A := (S : Subgroup H).map H.subtype
  let D := higherThompsonCenter (S : Subgroup H) (0+j)
  have hVA : V ≤ A := h.le_sylowCentralizer.trans hQA
  have hr := rank_bound h hVA hj
  have hVD : V ≤ higherThompsonCenter A j := by
    change V ≤ omegaOneCenterAmbient (thompsonJ A j)
    rw [← (lemma_B_2_3_2 A (le_refl j) hr).2]
    intro x hx
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl x
      ⟨hVA hx,(le_centralizer_iff.mp hJ) hx⟩
      (by let := h.elementary; exact elemPow_eq_one_of_isElementaryAbelian x hx)
  have hDmap : D.map H.subtype = higherThompsonCenter A j := by
    dsimp [D,higherThompsonCenter,A]
    rw [Nat.zero_add,thompsonJ_map_injective H.subtype H.subtype_injective,
      omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective]
  have hN := normalizer_thompson_le_of_control h hj hQA hAT hJ
  have hwhole := source_E_5_2_of_isEGenerated S 0 j hjpos hgen
  have hle : thompsonCentralizerGenerators (S : Subgroup H) 0 j ≤ M.comap H.subtype := by
    apply sup_le
    · apply map_le_iff_le_comap.mp
      apply (le_normalizer_map H.subtype).trans
      rw [← thompsonJ_map_injective H.subtype H.subtype_injective]
      exact hN
    · apply iSup_le
      intro d
      have hd : d.val ∈ smallIndexSubgroups D (0+j) := d.property
      have hi : Nat.log 2 ((V ⊓ d.val.map H.subtype).relIndex V) ≤ j := by
        rw [inf_relIndex_left]
        have hv : V ≤ D.map H.subtype := hDmap.symm ▸ hVD
        have hi := relIndex_le_of_le_right (H := d.val.map H.subtype) hv
          (show (d.val.map H.subtype).relIndex (D.map H.subtype) ≠ 0 from index_ne_zero_of_finite)
        have hl := Nat.log_mono_right (b := 2) hi
        rw [relIndex_map_map_of_injective _ _ H.subtype_injective] at hl
        exact hl.trans (by simpa only [Nat.zero_add] using hd.2)
      have hc : centralizer (V ⊓ d.val.map H.subtype : Set G) ≤ M :=
        (centralizer_le_normalizer_of_corank_lt_globalR inf_le_left
          (lt_of_le_of_lt (by exact_mod_cast hi) hj)).trans h.normalizer_le
      apply map_le_iff_le_comap.mp
      apply (map_mono (thompsonJ_le (centralizer (d.val : Set H)) 0)).trans
      apply (map_centralizer_le_centralizer_image (d.val : Set H) H.subtype).trans
      exact (centralizer_le inf_le_right).trans hc
  refine ⟨?_,normalizer_le_of_control h hj hQA hAT hJ⟩
  rw [hwhole] at hle
  intro x hx
  exact hle (show (⟨x,hx⟩ : H) ∈ (⊤ : Subgroup H) from mem_top _)
/-- The numerical form on the original carrier, after positive attainment. -/
theorem source_E_6_26_of_positive_parameter
    {κ : GroupClass.{u}} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 κ T M V) {j : ℕ}
    (H : Subgroup G) (S : Sylow 2 H) (hpos : 0 < generationParameter H)
    (hn : generationParameter H ≤ j)
    (hQA : sylowCentralizer (T : Subgroup G) V ≤ (S : Subgroup H).map H.subtype)
    (hAT : (S : Subgroup H).map H.subtype ≤ T)
    (hj : (j : ℕ∞) < globalR V)
    (hJ : thompsonJ ((S : Subgroup H).map H.subtype) j ≤ centralizer (V : Set G)) :
    H ≤ M ∧ normalizer ((S : Subgroup H).map H.subtype : Set G) ≤ M :=
  source_E_6_26_of_isEGenerated h (hpos.trans_le hn) H S
    ((isEGenerated_generationParameter_of_pos hpos).mono hn) hQA hAT hj hJ

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.SylowThompson
