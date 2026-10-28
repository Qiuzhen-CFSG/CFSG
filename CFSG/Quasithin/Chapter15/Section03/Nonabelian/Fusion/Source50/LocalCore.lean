module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Initial
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.CoreScalars
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.LayerFixed
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion.Kernel
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Assemble the literal local-core inputs from source 48, 53, 55 and 58

The common layer action already gives the order of the pair and the odd
quotient of Y. Its commutators put the entire pair core in Y, so the lower
module lies there as well. The original F.9 kernel and the source centers
then supply every input of the terminal local-core calculation.

Source: Aschbacher–Smith, proof of 15.3.59, printed pp.1149–1150.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core
open Core.Automizers.Models Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

 theorem localCoreData_of_layers (d : CharacteristicTwo.LocalData G)
    (h : (localSetup d (centralizerH d.Z)).Hypothesis)
    [(d.Z.subgroupOf (closureU d.Z d.ZS)).Normal]
    (g : G) [(d.V.subgroupOf (pairP d.Z d.ZS g)).Normal]
    (hI : pairI d.Z d.ZS g = d.Y ⊔ closureU d.Z d.ZS)
    (hIM : pairI d.Z d.ZS g ≤ d.M)
    (hVP : d.V ≤ pairP d.Z d.ZS g)
    (hcenterP : d.V = (center (pairP d.Z d.ZS g)).map (pairP d.Z d.ZS g).subtype)
    (hcenterU : center (closureU d.Z d.ZS) = d.Z.subgroupOf (closureU d.Z d.ZS))
    (hVC : d.V ⊓ centralizer (closureU d.Z d.ZS : Set G) = d.Z)
    (layers : LayerActions (pairI d.Z d.ZS g) d.Y (pairP d.Z d.ZS g) d.V
      (Cubic.MLocal.Structure.pairI_normalizes_pairP d.Z d.ZS g)
      (hIM.trans d.action.normalizes)) :
    LocalCoreData (d.T : Subgroup G) d.Z d.ZS d.V d.Y := by
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal d.M d.Mc)
  have hYI : d.Y ≤ pairI d.Z d.ZS g := hI ▸ le_sup_left
  have hPI : pairP d.Z d.ZS g ≤ pairI d.Z d.ZS g := map_subtype_le _
  have hIY := hIM.trans hMY
  have hPY := layers.core_le_Y hYI hPI hIY hVP
  have hUT : closureU d.Z d.ZS ≤ (d.T : Subgroup G) := h.UH_le_QH.trans h.QH_le_T
  have hU : IsPGroup 2 (closureU d.Z d.ZS) :=
    d.T.isPGroup'.to_le hUT
  have hZQ : d.Z ≤ closureU d.Z d.ZS := h.point_lt.le.trans (ZS_le_closureU _ _)
  have hYself : centralizer (pCore 2 d.Y : Set d.Y) ≤ pCore 2 d.Y := by
    rw [← h.characteristic_L]
    exact centralizer_generalizedFitting_le d.Y
  have hcoreY : (Stellmacher.twoCoreAmbient d.Y).subgroupOf d.Y = pCore 2 d.Y := by
    ext y
    constructor
    · rintro ⟨a,ha,he⟩
      exact Subtype.ext he ▸ ha
    · intro hy
      exact ⟨y,hy,rfl⟩
  have hYN : ((Stellmacher.twoCoreAmbient d.Y).subgroupOf d.Y).Normal := by
    rw [hcoreY]
    infer_instance
  have hcardY : Nat.card (d.Y ⧸ pCore 2 d.Y) = 9 :=
    layers.card_Y_quotient hYI hIY hVP rfl
  refine {
    two_group := d.T.isPGroup'
    T_le_H := h.T_le_H
    closure_le_core := h.UH_le_QH
    core_le_sylow := h.QH_le_T
    center_closure := ?_
    action_kernel := AbelianExclusion.source_kernel d.T d.Y d.V d.ZS d.Z h
    module_le_sylow := h.V_le_T
    normalizes_module := h.T_normalizes_V
    normalizes_Y := h.normalizes_L
    module_le_Y := hVP.trans hPY
    module_centralizer := hVC
    center_two_group := d.T.isPGroup'.to_le (centralInvolutions_le_sylow d.T)
    omega_le_module := le_conjugateSpanBy d.Z d.M
    normalizes_pair_core := le_sup_left.trans
      ((d.Y ⊔ closureU d.Z d.ZS).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
    pair_core_centralizer := ?_
    Y_core_normal := hYN
    Y_quotient_odd := ?_
    Y_perfect := residualY_isPPerfect d.M d.Mc
    Y_core_le_pair_core := pCoreIn_mono_of_normalizes le_sup_left
      (sup_le d.Y.le_normalizer (hUT.trans h.normalizes_L))
    module_fixed := LayerActions.lower_fixed_eq_bot layers
    pair_two_part := ?_ }
  · rw [hcenterU,map_subgroupOf_eq_of_le hZQ]
  · apply pair_core_centralizer_of_center d.Y (closureU d.Z d.ZS) d.V
      hYself hU (hUT.trans h.normalizes_L)
    have hP : pairP d.Z d.ZS g = (d.Y ⊔ closureU d.Z d.ZS).pCoreIn 2 := by
      change (pairI d.Z d.ZS g).pCoreIn 2 = _
      rw [hI]
    exact (congrArg (fun P : Subgroup G => (center P).map P.subtype) hP).symm.trans hcenterP.symm
  · let := hYN
    change Odd (Nat.card (d.Y ⧸ (Stellmacher.twoCoreAmbient d.Y).subgroupOf d.Y))
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hcoreY).toEquiv,hcardY]
    decide
  · rw [← hI]
    exact layers.twoPart_actor_domain hPI hVP

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50
