module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonPrepared

/-!
# Literal Case-I Thompson setup for original 15.1.15

The Case-I argument of original 15.1.15 starts with the actual chosen module
and its fixed subgroup `V_E = C_V(J₁(T))`. This leaf packages the preceding
15.1.12(4) and 15.1.13(1--2) conclusions for that literal subgroup:
nontriviality, containment in the first Thompson omega-center, centralization
by every actual outside-local residual, and the centralizer escape. The later
component argument can therefore retain the chosen moved support and does not
silently replace it by `V(M)`.

Source: Aschbacher--Smith 15.1.13(1--2), 15.1.14(1), and the setup of
15.1.15, printed pp.1090--1092.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The literal fixed subgroup used by Case I of original 15.1.15. -/
theorem PreparedChosenModule.caseI_thompson_setup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) :
    let J := ChapterB.thompsonJ (T : Subgroup G) 1
    let E := omegaOneCenterAmbient J
    let VE := thompsonFixed T V
    VE ≠ ⊥ ∧
      VE ≤ E ∧
      (∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
        (pResidual 2 H).map H.subtype ≤ centralizer (VE : Set G)) ∧
      ¬ centralizer (E : Set G) ≤ M ∧
      ⁅V,J⁆ ≠ ⊥ := by
  let J := ChapterB.thompsonJ (T : Subgroup G) 1
  let E := omegaOneCenterAmbient J
  let VE := thompsonFixed T V
  have hVE : VE ≠ ⊥ := by
    have hseed : centralInvolutions T ⊓ V ≤ VE := by
      refine le_inf inf_le_right ?_
      intro z hz j hj
      exact ((mem_omegaOneCenterAmbient_iff _ z).mp hz.1).2.2 j
        (ChapterB.thompsonJ_le _ _ hj)
    have hZ : centralInvolutions T ⊓ V ≠ ⊥ := by
      intro hz
      apply h.nontrivial
      rw [h.seed_span, hz]
      exact bot_unique (conjugateSpanBy_le bot_le (by
        change M ≤ normalizer (⊥ : Subgroup G)
        rw [normalizer_eq_top]
        exact le_top))
    exact fun hz => hZ (bot_unique (hseed.trans_eq hz))
  have hVEω : VE ≤ E := h.thompsonFixed_le_omega T hM
  have hres : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      (pResidual 2 H).map H.subtype ≤ centralizer (VE : Set G) :=
    h.source_thompsonFixed_local_residuals hG T hempty hM hJ
  have hm := h.source_thompson_escape_and_movement hG T hempty hM hmany hJ
  exact ⟨hVE, hVEω, hres, hm.1, hm.2⟩

end CFSG.Quasithin.Chapter15.Section01
