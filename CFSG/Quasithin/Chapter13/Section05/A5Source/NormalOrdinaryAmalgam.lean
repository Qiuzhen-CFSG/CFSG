module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalOrdinaryEndpoints
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.OverlapRigidity

/-!
# The compatible ordinary unitary amalgam in the original A₅ branch

Restrict the already marked point and plane endpoint equivalences to their
literal common Borel. Both restrictions carry the same original module V
to the same plane radical in the unitary overlap. Their discrepancy therefore
preserves that radical. The concrete overlap factorization removes it by
compatible endpoint automorphisms, retaining both original inclusion squares.

Every endpoint and overlap premise is proved from the original source Context,
earlier A.3.12, nonabelian U_H, residual normality and the ordinary condition
LT=L. The conclusion is a genuine RankTwoAmalgam.Iso, suitable for the source
ordinary completion recognition; it is stronger than separate endpoint maps.

Source: Aschbacher--Smith 13.5.17, printed p.922, ordinary U₄(2) branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.GreenBook.LieModels.UnitaryFour
open ChapterF.UnitaryTwo

private def endpointRestriction {G K : Type*} [Group G] [Group K]
    {S B : Subgroup G} {S' B' : Subgroup K} (h : B≤S) (h' : B'≤S')
    (e : S ≃* S') (he : (B.subgroupOf S).map e.toMonoidHom = B'.subgroupOf S') : B ≃* B' :=
  (subgroupOfEquivOfLe h).symm.trans ((e.subgroupMap _).trans
    ((MulEquiv.subgroupCongr he).trans (subgroupOfEquivOfLe h')))

private theorem endpointRestriction_val {G K : Type*} [Group G] [Group K]
    {S B : Subgroup G} {S' B' : Subgroup K} (h : B≤S) (h' : B'≤S')
    (e : S ≃* S') (he : (B.subgroupOf S).map e.toMonoidHom = B'.subgroupOf S') (b : B) :
    (endpointRestriction h h' e he b : K) = (e ⟨b,h b.property⟩ : K) := by rfl

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

/-- The original ordinary source inclusion amalgam is the literal binary
unitary amalgam, with both commuting squares. -/
theorem source_normal_ordinary_amalgam_unitary
    (hordinary : L ⊔ (T : Subgroup G) = L) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups H
        (residualCentralizer L V₁ ⊔ (T : Subgroup G)) (L ⊔ (T : Subgroup G))
        hH.1.2 (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl))
      (amalgam 1 (Nat.le_refl 1))) := by
  obtain ⟨v,hv,eP,hePv,hPcore,hPline,hPV,hPB⟩ :=
    source_normal_ordinary_point_unitary d hA312 hH hU hn hordinary
  obtain ⟨eR,hRV,hRline,hRB⟩ :=
    source_normal_ordinary_plane_unitary d hA312 hH hU hn hordinary
  let B := residualCentralizer L V₁ ⊔ (T : Subgroup G)
  let R := L ⊔ (T : Subgroup G)
  have hBP : B≤H := hH.1.2
  have hBR : B≤R := sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl
  have hBP' : overlap 1 (Nat.le_refl 1) ≤ pointParabolic 1 (Nat.le_refl 1) := by
    rw [←exact_overlap]; exact inf_le_left
  have hBR' : overlap 1 (Nat.le_refl 1) ≤ planeParabolic 1 (Nat.le_refl 1) := by
    rw [←exact_overlap]; exact inf_le_right
  let uP := endpointRestriction hBP hBP' eP hPB
  let uR := endpointRestriction hBR hBR' eR hRB
  have hP (b : B) : (uP b : ProjectiveGroup 1 (Nat.le_refl 1))∈InvolutionPlacement.planeCore ↔ (b:G)∈V := by
    rw [endpointRestriction_val]
    change eP ⟨b,hBP b.property⟩ ∈ PointInvolution.pointModule ↔ _
    rw [←hPV,mem_map_equiv,eP.symm_apply_apply]
    rfl
  have hR (b : B) : (uR b : ProjectiveGroup 1 (Nat.le_refl 1))∈InvolutionPlacement.planeCore ↔ (b:G)∈V := by
    rw [endpointRestriction_val,OverlapRigidity.planeCore_mem,←hRV,
      mem_map_equiv,eR.symm_apply_apply]
    rfl
  let δ := uP.symm.trans uR
  have hf : FactorsThrough (amalgam 1 (Nat.le_refl 1)) δ := by
    apply OverlapRigidity.factorsThrough_marked
    intro b hb
    change (uR (uP.symm b) : ProjectiveGroup 1 (Nat.le_refl 1))∈InvolutionPlacement.planeCore
    apply (hR _).mpr
    apply (hP _).mp
    simpa only [MulEquiv.apply_symm_apply] using hb
  let f : Iso (RankTwoAmalgam.ofSubgroups H B R hBP hBR)
      (twistRight (amalgam 1 (Nat.le_refl 1)) δ) := {
    left := eP
    middle := uP
    right := eR
    left_commutes b := by
      apply Subtype.ext
      exact (endpointRestriction_val hBP hBP' eP hPB b).symm
    right_commutes b := by
      apply Subtype.ext
      change (eR ⟨b,hBR b.property⟩ : ProjectiveGroup 1 (Nat.le_refl 1)) =
        (uR (uP.symm (uP b)) : ProjectiveGroup 1 (Nat.le_refl 1))
      rw [uP.symm_apply_apply]
      exact (endpointRestriction_val hBR hBR' eR hRB b).symm }
  exact ⟨f.trans hf.iso⟩
end CFSG.Quasithin.Chapter13.Section05.A5Source
