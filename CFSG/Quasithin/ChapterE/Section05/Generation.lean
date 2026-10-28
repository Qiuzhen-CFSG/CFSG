module
public import CFSG.Quasithin.ChapterE.Section05.Basic
public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.GroupTheory.ConjugacyFamilyFrattini
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The Frattini and E-generation steps of E.5.2

Sylow conjugacy identifies the two-rank in the Sylow subgroup with the
ambient two-rank. The global Thompson family can therefore be used for
weak closure. The relative Frattini argument then controls each centralizer
appearing in E.5.2 by its own Thompson subgroup and the fixed Thompson
normalizer.

The final reduction applies the actual E-generation parameter: to obtain
the asserted generation, it remains to place the two-residual of every
local E-member in the displayed subgroup. This premise is explicit; this
module does not assert the completed Proposition E.5.2.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Proposition E.5.2, printed p.243.
-/

open Subgroup Stellmacher CFSG.Quasithin.ChapterB
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

public theorem twoRank_sylow (P : Sylow 2 G) :
    twoRank (P : Subgroup G) = twoRank (⊤ : Subgroup G) := by
  apply congrArg (Nat.log 2)
  apply le_antisymm (elementaryAbelianMaxOrder_le_and_j_le_of_eq _ _ le_top).1
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty (P : Subgroup G)
  obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty (⊤ : Subgroup G)
  obtain ⟨S, hBS⟩ := hB.2.1.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  let e := MulAut.conj g
  have hSP : (S : Subgroup G).map e.toMonoidHom = (P : Subgroup G) := by
    change ((g • S : Sylow 2 G) : Subgroup G) = (P : Subgroup G)
    rw [hg]
  have hc := hA.2.2 (B.map e.toMonoidHom) ((map_mono hBS).trans hSP.le)
    (hB.2.1.map e.toMonoidHom)
  rwa [card_map_of_injective e.injective,
    elementaryAbelianMaxSubgroups_card_eq _ _ hB,
    elementaryAbelianMaxSubgroups_card_eq _ _ hA] at hc

public theorem thompsonFamily_top_invariant (i : ℕ) :
    SubgroupFamily.ConjugationInvariant (thompsonFamily (⊤ : Subgroup G) i) := by
  intro A hA g
  let _ : IsElementaryAbelian 2 A := hA.2.1
  exact ⟨le_top, IsElementaryAbelian.map _, hA.2.2.1,
    (card_map_of_injective (MulAut.conj g).injective).trans hA.2.2.2⟩

public theorem span_thompsonFamily_top (H : Subgroup G) (i : ℕ)
    (hr : twoRank H = twoRank (⊤ : Subgroup G)) :
    SubgroupFamily.span (thompsonFamily (⊤ : Subgroup G) i) H = thompsonJ H i := by
  apply congrArg sSup
  ext A
  constructor
  · intro ⟨hA, hAH⟩
    exact ⟨hAH, hA.2.1, hr ▸ hA.2.2⟩
  · intro hA
    exact ⟨⟨le_top, hA.2.1, hr ▸ hA.2.2⟩, hA.1⟩

/-- The Frattini step in E.5.2 works in every overgroup of `Jᵢ(P)`. -/
public theorem thompson_frattini_of_le (P : Sylow 2 G) (H : Subgroup G) (i : ℕ)
    (hi : i < twoRank (P : Subgroup G)) (hJH : thompsonJ (P : Subgroup G) i ≤ H) :
    H ≤ normalizer (thompsonJ (P : Subgroup G) i : Set G) ⊔ thompsonJ H i := by
  have h0 : elementaryAbelianMaxJ (P : Subgroup G) ≤ H := by
    rw [← thompsonJ_zero]
    exact (lemma_B_2_3_1 _ (Nat.zero_le i) hi).trans hJH
  have hr : twoRank H = twoRank (⊤ : Subgroup G) := by
    apply le_antisymm
    · exact Nat.log_mono_right (elementaryAbelianMaxOrder_le_and_j_le_of_eq H ⊤ le_top).1
    · rw [← twoRank_sylow P]
      exact Nat.log_mono_right
        (elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le _ H h0).1
  have hpJ : IsPGroup 2 (thompsonJ (P : Subgroup G) i) :=
    P.2.of_injective (Subgroup.inclusion (thompsonJ_le _ i))
      (Subgroup.inclusion_injective _)
  obtain ⟨S, hJS⟩ := (show IsPGroup 2 ((thompsonJ (P : Subgroup G) i).subgroupOf H) from hpJ.comap_subtype).exists_le_sylow
  have hJY : thompsonJ (P : Subgroup G) i ≤ (S : Subgroup H).map H.subtype := by
    have h := map_mono (f := H.subtype) hJS
    rwa [map_subgroupOf_eq_of_le hJH] at h
  have he := SubgroupFamily.span_eq_in_p_overgroup (thompsonFamily_top_invariant i) P
    ((S : Subgroup H).map H.subtype) (S.2.map H.subtype)
    ((span_thompsonFamily_top _ i (twoRank_sylow P)).le.trans hJY)
  have hf := SubgroupFamily.relative_frattini (thompsonFamily_top_invariant i) H S
  rw [← he, span_thompsonFamily_top _ i (twoRank_sylow P), span_thompsonFamily_top H i hr] at hf
  exact hf

public theorem centralizer_le_thompsonCentralizerGenerators (P : Sylow 2 G) (i j : ℕ)
    (hij : i + j < twoRank (P : Subgroup G)) (D₁ : Subgroup G)
    (hD₁ : D₁ ∈ smallIndexSubgroups (higherThompsonCenter (P : Subgroup G) (i + j)) (i + j)) :
    centralizer (D₁ : Set G) ≤ thompsonCentralizerGenerators (P : Subgroup G) i j := by
  have hJD : thompsonJ (P : Subgroup G) i ≤ centralizer (D₁ : Set G) := by
    apply (lemma_B_2_3_1 _ (Nat.le_add_right i j) hij).trans
    apply (le_centralizer_iff.mp (higherThompsonCenter_centralizes _ _)).trans
    exact centralizer_le hD₁.1
  apply (thompson_frattini_of_le P _ i (by omega) hJD).trans
  apply sup_le le_sup_left
  exact le_sup_of_le_right (le_iSup_of_le ⟨D₁, hD₁⟩ le_rfl)

/-- An E-member is controlled once its residual and the ambient Sylow subgroup are. -/
public theorem IsEMember.le_of_residual_le {P A K M : Subgroup G}
    (hK : IsEMember P A K) (hP : P ≤ M)
    (hR : (pResidual 2 K).map K.subtype ≤ M) : K ≤ M := by
  obtain ⟨S, hS⟩ := hK.2.2.2.2.1
  have he := congrArg (fun U : Subgroup K => U.map K.subtype)
    (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, hS, subgroupOf_map_subtype,
    ← MonoidHom.range_eq_map, range_subtype] at he
  exact he.ge.trans (sup_le hR (inf_le_left.trans hP))

/-- The E-generation step of E.5.2. The remaining local obligation is explicitly
control of each E-member's two-residual, not the desired global generation. -/
public theorem eq_top_of_thompson_residuals (P : Sylow 2 G) (i j : ℕ)
    (hgen : IsEGenerated j G) (M : Subgroup G)
    (hN : normalizer (thompsonJ (P : Subgroup G) i : Set G) ≤ M)
    (hR : ∀ A K : Subgroup G, A ∈ thompsonFamily (P : Subgroup G) i →
      IsEMemberAt j (P : Subgroup G) A K → (pResidual 2 K).map K.subtype ≤ M) :
    M = ⊤ := by
  let Ω := thompsonFamily (⊤ : Subgroup G) i
  have hΩ : IsElementaryFamily Ω := ⟨fun _ hA => hA.2.1,
    fun g A hA => thompsonFamily_top_invariant i A hA g⟩
  have hWP : weakClosure (P : Subgroup G) Ω = thompsonJ (P : Subgroup G) i :=
    span_thompsonFamily_top _ i (twoRank_sylow P)
  have hPM : (P : Subgroup G) ≤ M :=
    (P : Subgroup G).le_normalizer.trans
      ((normalizer_le_normalizer_thompsonJ _ i).trans hN)
  have he : eFamilySubgroup j (P : Subgroup G) Ω ≤ M := by
    apply iSup_le
    intro A
    apply sSup_le
    intro K hK
    have hA : A.val ∈ thompsonFamily (P : Subgroup G) i :=
      ⟨A.property.2, A.property.1.2.1, (twoRank_sylow P) ▸ A.property.1.2.2⟩
    exact hK.1.le_of_residual_le hPM (hR A.val K hA hK)
  have hg := hgen P Ω hΩ
  rw [hWP] at hg
  exact top_unique (hg ▸ sup_le he hN)

/-- Conditional assembly for E.5.2, valid for every positive attained parameter.
The source section owner must discharge the displayed local residual bounds. -/
public theorem thompsonCentralizerGenerators_eq_top_of_residuals
    (P : Sylow 2 G) (i j : ℕ) (hj : 0 < j) (hn : generationParameter G = j)
    (hR : ∀ A K : Subgroup G, A ∈ thompsonFamily (P : Subgroup G) i →
      IsEMemberAt j (P : Subgroup G) A K → (pResidual 2 K).map K.subtype ≤
        thompsonCentralizerGenerators (P : Subgroup G) i j) :
    thompsonCentralizerGenerators (P : Subgroup G) i j = ⊤ := by
  have hg := isEGenerated_generationParameter_of_pos (G := G) (hn ▸ hj)
  rw [hn] at hg
  exact eq_top_of_thompson_residuals P i j hg _ le_sup_left hR

end CFSG.Quasithin.ChapterE
