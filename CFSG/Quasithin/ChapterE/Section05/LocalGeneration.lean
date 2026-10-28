module

public import CFSG.Quasithin.ChapterE.Section05.Generation
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import Theory.GroupTheory.ConjugateCentralizerCover

/-!
# Local centralizer covers and residual control

The normal-generation theorem E.1.4 turns control of the K-conjugates of A
into control of O²(K). A normal elementary overgroup of D and a small-index
subgroup centralized by A give such control via conjugate centralizers.
These are the last steps of the noncentral local case in E.5.2; construction
of that overgroup and its index bound remain separate obligations.

We also prove that the generation conclusion is automatic when i+j reaches
the two-rank, and that centralizing D by O²(G) makes D normal, using the
Sylow/residual product. The latter is the normality implication in E.5.4.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), E.5.2–4, printed pp.243–244.
-/

open Subgroup

namespace CFSG.Quasithin.ChapterE
open ChapterB
variable {G : Type*} [Group G] [Finite G]

public theorem IsEMember.residual_le_of_conjugates_le {P A K M : Subgroup G}
    (hK : IsEMember P A K)
    (hAM : ∀ k ∈ K, A.map (MulAut.conj k).toMonoidHom ≤ M) :
    (pResidual 2 K).map K.subtype ≤ M := by
  have hA : (A.subgroupOf K : Set K) ⊆ (M.subgroupOf K).normalCore := by
    intro a ha k
    exact hAM k k.property (mem_map_of_mem (MulAut.conj (k : G)).toMonoidHom ha)
  have hR := hK.residual_le_normalClosure.trans
    ((normalClosure_le_normal hA).trans (normalCore_le _))
  rintro _ ⟨r, hr, rfl⟩
  exact hR hr

public theorem residual_le_thompsonCentralizerGenerators_of_cover
    (P : Sylow 2 G) (i j : ℕ) (hij : i + j < twoRank (P : Subgroup G))
    (A K E E₁ : Subgroup G) (hK : IsEMember (P : Subgroup G) A K)
    (hDE : higherThompsonCenter (P : Subgroup G) (i + j) ≤ E)
    (hKE : K ≤ normalizer (E : Set G))
    (hAE₁ : A ≤ centralizer (E₁ : Set G))
    (hr : Nat.log 2 (E₁.relIndex E) ≤ i + j) :
    (pResidual 2 K).map K.subtype ≤
      thompsonCentralizerGenerators (P : Subgroup G) i j := by
  apply hK.residual_le_of_conjugates_le
  intro k hk
  obtain ⟨D₁, hD₁D, hindex, hcent⟩ :=
    conjugate_centralizer_cover _ E E₁ A K hDE hKE hAE₁ k hk
  exact hcent.trans (centralizer_le_thompsonCentralizerGenerators P i j hij D₁
    ⟨hD₁D, (Nat.log_mono_right hindex).trans hr⟩)

public theorem thompsonCentralizerGenerators_eq_top_of_rank_le
    (P : Sylow 2 G) (i j : ℕ) (hij : twoRank (P : Subgroup G) ≤ i + j) :
    thompsonCentralizerGenerators (P : Subgroup G) i j = ⊤ := by
  have hD : higherThompsonCenter (P : Subgroup G) (i + j) = ⊥ :=
    higherThompsonCenter_eq_bot_of_rank_le _ _ hij
  by_cases hi : twoRank (P : Subgroup G) ≤ i
  · unfold thompsonCentralizerGenerators
    rw [thompsonJ_eq_bot_of_rank_le _ _ hi]
    rw [normalizer_eq_top, top_sup_eq]
  · have hf := thompson_frattini_of_le P ⊤ i (by omega) le_top
    apply top_unique
    apply hf.trans
    apply sup_le le_sup_left
    have hmem : (⊥ : Subgroup G) ∈ smallIndexSubgroups
        (higherThompsonCenter (P : Subgroup G) (i + j)) (i + j) := by
      simp [smallIndexSubgroups, hD]
    apply le_sup_of_le_right
    have hle : thompsonJ (centralizer ((⊥ : Subgroup G) : Set G)) i ≤
        ⨆ D₁ : {D₁ : Subgroup G // D₁ ∈ smallIndexSubgroups
          (higherThompsonCenter (P : Subgroup G) (i + j)) (i + j)},
          thompsonJ (centralizer (D₁.val : Set G)) i :=
      le_iSup_of_le ⟨⊥, hmem⟩ le_rfl
    have hcent : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup G) ≤ center G from bot_le)
    rwa [hcent] at hle

public theorem higherThompsonCenter_normal_of_residual_centralizes
    (P : Sylow 2 G) (j : ℕ)
    (hC : pResidual 2 G ≤ centralizer (higherThompsonCenter (P : Subgroup G) j : Set G)) :
    (higherThompsonCenter (P : Subgroup G) j).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← pResidual_sup_sylow_eq_top P]
  exact sup_le (hC.trans (Subgroup.centralizer_le_normalizer _))
    ((P : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_higherThompsonCenter _ j))

end CFSG.Quasithin.ChapterE
