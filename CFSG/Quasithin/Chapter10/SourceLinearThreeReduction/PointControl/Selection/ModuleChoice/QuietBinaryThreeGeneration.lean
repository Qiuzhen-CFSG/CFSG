module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorEscape
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.LinearThree.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.LocalSource

/-!
# The quiet binary-three H-star generation bound

Apply the completed non-A₅ Hall-faithfulness theorem to the literal odd
Hall subgroup of H intersect M. The actual SL₃(2) quotient places its
faithful image in the original component orbit. Proper-overgroup control
makes it a three-group, and the proved three-Hall generation theorem gives
n(H) at most two.

This is the bound from 7.3.4 used in the Suzuki branch of 8.3.7. It assumes
the original minimal setup, quiet Thompson action and an actual isomorphism
from L/O₂(L) to SL₃(2). It does not assume the whole C_M(V) is a two-group,
and does not use the later 8.3.10 factorization. The tensor marking and the
remaining Suzuki exclusion are discharged by qt-d-10-nona5-point-selection;
final point-control assembly remains with qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 7.3.4, 8.3.7 and 10.2.3(ii), pp.699,724--725,745.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original quiet binary-three row has H-star generation parameter at
most two. The complete Hall-faithfulness theorem is used only on the actual
overlap Hall subgroup; no assertion about all of C_M(V) is made. -/
theorem quiet_binaryThree_hstar_generation_le_two
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    generationParameter H ≤ 2 := by
  by_cases hlarge : 1 < generationParameter H
  · have hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
      rintro ⟨a⟩
      have hc := Nat.card_congr (cL.symm.trans a).toEquiv
      rw [Matrix.PSL3Two.card_SL,nat_card_alternatingGroup] at hc
      norm_num [Nat.factorial] at hc
    obtain ⟨hP,_,_,_,d,he,hperm,_⟩ :=
      source_hstar_cartan_data_of_generation_gt_one D hH hlarge
    have hBM := he ▸ d.hall_le
    have hHall := he ▸ d.hall
    have hfaith := source_nonnormalHallFaithful hmany L D hmin hn hna H hH hlarge
      d.witness.abelianGroup hBM hHall d.witness.abelian hperm
    have hcentral : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (quiet_hstar_centralizes_omega D hJ hH)
    let c : CentralHall.Context D H d.witness.abelianGroup :=
      ⟨hmany,hmin,hn,hna,hH,hlarge,hcentral,hBM,hHall,d.witness.abelian,hperm,hfaith⟩
    have hthree : IsPGroup 3 d.witness.abelianGroup :=
      CentralHall.isThreeGroup_of_image D _ hBM hfaith
        (CentralHall.LinearThree.source_image_isThreeGroup D c cL)
    exact generationParameter_le_two_of_three_hall
      (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1)
      (T.subtype hH.1.1.2) hP d.witness.abelianGroup d.hall_le d.hall hthree
  · omega

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
