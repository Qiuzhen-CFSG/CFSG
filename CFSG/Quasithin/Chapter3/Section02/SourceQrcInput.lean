module
public import CFSG.Quasithin.Chapter3.Section02.SourceLocalConsequences
public import CFSG.Quasithin.Chapter3.Section02.QrcInput

/-!
# The qrc configuration for both original FSU actor alternatives

The local source module is reduced and its Sylow centralizer is O₂(XT).
The original residual and normality hypotheses identify O²(XT) with X,
so case (I) of Hypothesis 3.1.5 holds for every H in H*(T,M).
Uniqueness excludes the common-normal branch and supplies the literal
D.1.1 configuration. The nonzero seed also proves O₂(XT) is nontrivial.

These are the genuine hypotheses for 3.1.8. Its rank bounds and the
later D.3.10 classification still require their independent source proofs.
Source: Aschbacher–Smith, Lemma 3.2.2(9), combined manuscript
of 1 March 2004, printed pp.576 and 579.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M) (hTM : (T : Subgroup G) ≤ M)
  [(X.subgroupOf M).Normal]
  (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
  (hX : pResidual 2 (X.subgroupOf M) = ⊤)
  (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
    le_normalizer_of_normal)
  (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup (X ⊔ (T : Subgroup G)))))
  (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
    (X.subgroupOf (X ⊔ (T : Subgroup G))) I)

local notation "V₀" => ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I
local notation "V_T" => componentOrbit V₀ (T : Subgroup G)

include hXM hTM hG hM hX hc hI

theorem source_reduced_seed_local_core_ne_bot : (X ⊔ (T : Subgroup G)).pCoreIn 2 ≠ ⊥ := by
  intro he
  have hv : V_T = ⊥ := bot_unique
    ((source_reduced_seed_local_le_core T X M hXM hTM hG hM hX hc I hI).trans_eq he)
  exact ReducedNormal.subspaceImage_ne_bot _ _ (hI.ne_bot _)
    (bot_unique ((le_componentOrbit V₀ T).trans_eq hv))

theorem source_reduced_seed_qrc_hypotheses
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M) :
    Chapter3.QrcHypotheses T M (X ⊔ (T : Subgroup G)) Y V_T := by
  have hv := source_reduced_seed_local_le_core T X M hXM hTM hG hM hX hc I hI
  have hn := source_reduced_seed_local_normalizes T X M hXM hTM hG hM hX hc I hI
  have hi := source_reduced_seed_local_internal T X M hXM hTM hG hM hX hc I hI
  let H := X ⊔ (T : Subgroup G)
  let A := X.subgroupOf H
  let S : Sylow 2 H := T.subtype le_sup_right
  let := hi.normal
  have hgen : A ⊔ (S : Subgroup H) = ⊤ := by
    change X.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hR : pResidual 2 H = A := pResidual_eq_of_isPPerfect_sup A S
    ((pResidual_eq_top_iff 2 A).mp hi.residual) S.isPGroup' hgen
  have hMX : M ≤ normalizer (X : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hXM).mp inferInstance
  refine ⟨le_sup_right, sup_le hXM hTM, hY, hv.trans (pCoreIn_le 2 _), hn,
    source_reduced_seed_local_elementary T X M hXM hTM hG hM hX hc I hI, ?_,
    (source_reduced_seed_local_centralizer T X M hXM hTM hG hM hX hc I hI).symm,
    Or.inl ?_⟩
  · exact internalActionImage_core_of_reduced _ _ (hv.trans (pCoreIn_le 2 _)) hn
      (source_reduced_seed_local_reduced T X M hXM hTM hG hM hX hc I hI)
  · change Y ⊓ M ≤ normalizer ((pResidual 2 H).map H.subtype : Set G)
    rw [hR, map_subgroupOf_eq_of_le (show X ≤ H from le_sup_left)]
    exact inf_le_right.trans hMX

theorem source_reduced_seed_qrc_configuration
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M)
    {Y : Subgroup G} (hY : Y ∈ Chapter3.HStar (T : Subgroup G) M) :
    ChapterD.QRCConfiguration (X ⊔ (T : Subgroup G)) Y (T : Subgroup G) V_T := by
  have hq := source_reduced_seed_qrc_hypotheses T X M hXM hTM hG hM hX hc I hI hY
  exact hq.toQRCConfiguration (hq.no_common_normal hu)

end CFSG.Quasithin.Chapter3.Section02
