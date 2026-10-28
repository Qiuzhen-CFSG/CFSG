module
public import CFSG.Quasithin.Chapter14.Section02.RankTwoEntry
public import CFSG.Quasithin.Chapter12.Section08.Setup.Completion
/-!
# Original 14.2.5--6 on the actual outside family

The proved rank-two source setup constructs its invariant flag. Its point
is the original Ω₁(Z(T)), its first residual is trivial, and 14.2.3
identifies H_z with the actual H(T,M). Thus every original outside subgroup
satisfies G.2.1. Apply the proved local-closure and kernel theorems to the
same flag and quotient: the closure lies in the central omega of the local
two-core, is reduced, has Frattini subgroup in Z, and its tilde action has
precisely O₂(H) as kernel. No flag, kernel, or module conclusion is assumed.
Source: Aschbacher--Smith 14.2.5--6, printed p.982, and 12.8.3--4,
printed pp.849--850.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

theorem source_lemma_14_2_6
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3)) :
    ∃ he : IsElementaryAbelian 2 (rankTwoSeed T M), letI := he
    ∃ F : InvariantFlag T (rankTwoSeed T M) 2,
      F.Vi 1 = centralInvolutions T ∧ F.Li (sourceResidual M Mc) 1 = ⊥ ∧
      F.Hz (sourceResidual M Mc) M = Chapter1.HOutside G (T : Set G) (M : Set G) ∧
      ∀ H, H ∈ Chapter1.HOutside G (T : Set G) (M : Set G) → ∃ hHF : H ≤ F.H,
        ChapterG.Section02.Setup.Hypothesis
          { V := rankTwoSeed T M, V₁ := F.Vi 1, L := sourceResidual M Mc,
            T := (T : Subgroup G), H := H } ∧
        F.tilde (F.UH H) ≤ omegaOneAmbient
          ((center (F.tilde (H.pCoreIn 2))).map (F.tilde (H.pCoreIn 2)).subtype) ∧
        (frattini (F.UH H)).map (F.UH H).subtype ≤ centralInvolutions T ∧
        IsPReduced 2 ((F.tilde (F.UH H)).subgroupOf (F.tilde H)) ∧
        (F.localTildeAction H hHF).ker = pCore 2 H := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let he := rankTwoSeed_elementary h
  let := he
  obtain ⟨_,F,_⟩ := h.exists_flag_geometry
  have hp : F.Vi 1 = centralInvolutions T :=
    (h.sylowOmega_eq_point F).symm.trans (sylowOmega_eq_centralInvolutions T)
  have hL := h.Li_one_eq_bot F
  have hFH : F.H = centralizer (centralInvolutions T : Set G) := by
    change normalizer (F.Vi 1 : Set G) = _
    rw [hp]
    exact le_antisymm (normalizer_le_centralizer_of_card_two _
      (plane_centralInvolutions_card T M hM.1.2 hcard e)) (Subgroup.centralizer_le_normalizer _)
  have hHz : F.Hz (sourceResidual M Mc) M = Chapter1.HOutside G (T : Set G) (M : Set G) := by
    ext H
    constructor
    · rintro ⟨hH,_,hout⟩
      exact ⟨⟨hH.1,fun x hx => hH.2 (Or.inr hx)⟩,hout⟩
    · rintro ⟨hH,hout⟩
      have hLH : F.Li (sourceResidual M Mc) 1 ≤ H := by rw [hL]; exact bot_le
      refine ⟨⟨hH.1,fun x hx => hx.elim (fun hx => hLH hx) (fun hx => hH.2 hx)⟩,?_,hout⟩
      change H ≤ F.H
      rw [hFH]
      exact (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH hout).2
  refine ⟨he,F,hp,hL,hHz,?_⟩
  intro H hH
  have hJ : H ∈ F.Hz (sourceResidual M Mc) M := hHz.symm ▸ hH
  have hnat : 3 ≤ 2 → Nonempty (InvariantFlag.AmbientNaturalMarking (sourceResidual M Mc) h.L_normalizes_seed 2) := by omega
  have hclose := F.localKernel_closure hG _ M H (by decide) h.seed_le_sylow h.L_normalizes_seed
    h.sylow_normalizes_L h.L_residual hnat hJ
  refine ⟨hJ.2.1,F.localKernel_hypothesis hG _ M H (by decide) h.seed_le_sylow h.L_normalizes_seed
    h.sylow_normalizes_L h.L_residual hnat hJ,hclose.1.2,hclose.2.1.trans_eq hp,hclose.2.2.2,?_⟩
  exact F.localKernel_eq_pCore hG _ M H (by decide) h.seed_le_sylow h.L_normalizes_seed
    h.sylow_normalizes_L h.L_residual hnat h.M_eq_normalizer h.unique h.seed_centralizer_le h.centralizer_L hJ
end CFSG.Quasithin.Chapter14.Section02
