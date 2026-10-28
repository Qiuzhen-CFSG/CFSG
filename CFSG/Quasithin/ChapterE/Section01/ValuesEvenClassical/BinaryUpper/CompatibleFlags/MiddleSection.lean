module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.BinaryUpper.CompatibleFlags.Alignment
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Flags
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.BinaryUpper.LocalStructure
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The binary middle flag's PSL₃ section

The literal five-dimensional middle flag has cuts of dimensions one and four.
Its diagonal action has block sizes 1+3+1. The one-dimensional binary factors
are trivial, and coordinates on the middle block identify the quotient by the
flag's intrinsic two-core with the actual PSL₃(2) model.

For an aligned marking, this parabolic P is normal in its ambient flag H = PT,
including the graph case. Set Q = O₂(H). Restriction of the two-core to P gives
P ∩ Q = O₂(P), so the image of P in H/Q is the displayed simple group. The
image of T supplements it and is a two-group. Since O₂(H/Q) is trivial, the
simple-normal-subgroup theorem identifies this image with F*(H/Q). Extending
the image of T to a Sylow subgroup supplies the required actual supplement.
The whole quotient is allowed to contain the induced graph automorphism.

This constructs the local structural input for the supplied marking in the
binary E-generation argument. Source: Aschbacher--Smith, *The Classification
of Quasithin Groups*, E.1.14(1), printed p.214, citing Aschbacher (1982),
Lemma 4.7, DOI 10.2307/2374202.
-/

public section

open Subgroup
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
open BinaryLinear.SmallParabolicLevi.TwoNodes
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper.MiddleSection

private def cuts : Set (Fin 4) := {0, 3}
private def labels : Fin 5 → Fin 5 := ![0, 1, 1, 1, 2]

private theorem univ_four : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide

private theorem cutLabel_eq : cutLabel cuts = labels := by
  funext i
  fin_cases i <;> simp [cutLabel, cuts, labels, univ_four, Finset.filter_insert, Finset.filter_singleton]

private theorem block_card (k : Fin 5) :
    Fintype.card (Block labels k) = if k = 1 then 3 else if k = 0 ∨ k = 2 then 1 else 0 := by
  fin_cases k <;> decide

private noncomputable def blockCoordinates (k : Fin 5) :
    BlockSpace labels k ≃ₗ[ZMod 2] Space (Fintype.card (Block labels k)) :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (Fintype.equivFin (Block labels k)).symm

private noncomputable def middleCoordinates : BlockSpace labels 1 ≃ₗ[ZMod 2] Space 3 :=
  (blockCoordinates 1).trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2)
    (finCongr (by simp [block_card] : Fintype.card (Block labels 1) = 3)).symm)

private theorem otherFactor_subsingleton (k : Fin 5) (hk : k ≠ 1) :
    Subsingleton (BinaryLinear.GL (BlockSpace labels k)) := by
  apply (Nat.card_eq_one_iff_unique.mp ?_).1
  have hn : Fintype.card (Block labels k) ≤ 1 := by
    rw [block_card]
    split_ifs <;> omega
  rw [Nat.card_congr (linearGroupCongr (blockCoordinates k)).toEquiv]
  generalize Fintype.card (Block labels k) = n at hn ⊢
  interval_cases n <;>
    rw [← Nat.card_congr (matrixEquivLinear _).toEquiv, Matrix.card_GL_field] <;> simp

private noncomputable def middleEvaluation :
    (∀ k : Fin 5, BinaryLinear.GL (BlockSpace labels k)) ≃*
      BinaryLinear.GL (BlockSpace labels 1) :=
  MulEquiv.ofBijective (Pi.evalMonoidHom (fun k : Fin 5 => BinaryLinear.GL (BlockSpace labels k)) 1)
    ⟨by
      intro a b hab
      funext k
      by_cases hk : k = 1
      · subst k; exact hab
      · exact @Subsingleton.elim _ (otherFactor_subsingleton k hk) (a k) (b k),
    by
      classical
      intro a
      refine ⟨Function.update 1 1 a, ?_⟩
      change Function.update (1 : ∀ k : Fin 5, BinaryLinear.GL (BlockSpace labels k)) 1 a 1 = a
      exact Function.update_self ..⟩

private theorem projectiveMiddle_map :
    (projectiveParabolic 5 (middleRoots 5)).map (linearComparison 5).toMonoidHom =
      BinaryLinear.FiveFlagGeometry.flagStabilizer (coordinateBasis 4) cuts := by
  rw [map_projectiveParabolic_linear]
  have he : {i : Fin 4 | i.val ∉ middleRoots 5} = cuts := by
    ext i
    fin_cases i <;> simp [cuts, middleRoots]
  rw [he]
  rfl

/-- The actual middle parabolic modulo its intrinsic two-core is PSL₃(2),
via its three-dimensional diagonal block. -/
noncomputable def projectiveMiddleQuotientEquiv :
    (projectiveParabolic 5 (middleRoots 5) ⧸ pCore 2 (projectiveParabolic 5 (middleRoots 5))) ≃*
      PSL 3 := by
  let a := ((linearComparison 5).subgroupMap (projectiveParabolic 5 (middleRoots 5))).trans
    (MulEquiv.subgroupCongr projectiveMiddle_map)
  let q := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let b := flagDiagonalQuotientEquiv (coordinateBasis 4) cuts
  rw [cutLabel_eq] at b
  exact q.trans (b.trans (middleEvaluation.trans
    ((linearGroupCongr middleCoordinates).trans linearThreeEquivProjective)))

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper.MiddleSection

open Subgroup
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper.MiddleSection

/-- Adjoining a two-group to a normal group with the indicated PSL₃ quotient
gives the required middle section after factoring out the ambient two-core. -/
theorem hasSection_of_normal {H : Type*} [Group H] [Finite H]
    (P R : Subgroup H) [P.Normal] (hR : IsPGroup 2 R) (hsup : P ⊔ R = ⊤)
    (e : (P ⧸ pCore 2 P) ≃* PSL 3) : HasBinaryMiddleSection H := by
  let : IsSimpleGroup (PSL 3) := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup 3) :=
    BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let a := BinaryLinear.SmallParabolicLevi.linearThreeEquivProjective
  let : Group.IsPerfect (PSL 3) :=
    Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
  let q := QuotientGroup.mk' (pCore 2 H)
  let N := P.map q
  let f := q.subgroupMap P
  have hker : f.ker = pCore 2 P := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 (inferInstance : P.Normal).isSubnormal).symm
  let c : (P ⧸ pCore 2 P) ≃* N :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective P))
  let en : N ≃* PSL 3 := c.symm.trans e
  let : N.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup N := en.isSimpleGroup
  let : Group.IsPerfect N :=
    Group.IsPerfect.ofSurjective (f := en.symm.toMonoidHom) en.symm.surjective
  have hgen : N ⊔ R.map q = ⊤ := by
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hquot : IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (R.map q) (hR.map q) hgen
  have hGF : generalizedFitting (H ⧸ pCore 2 H) = N :=
    (simple_two_quotient_structure N (Group.IsPerfect.not_isMulCommutative N) hquot
      (pCore_quotient_pCore_eq_bot 2)).1
  let eg : generalizedFitting (H ⧸ pCore 2 H) ≃* PSL 3 :=
    (MulEquiv.subgroupCongr hGF).trans en
  obtain ⟨S, hS⟩ := (hR.map q).exists_le_sylow
  refine ⟨pCore 2 H, inferInstance, pCore_isPGroup, eg.isSimpleGroup, ⟨eg⟩, S, ?_⟩
  rw [hGF]
  exact top_unique (hgen ▸ sup_le_sup_left hS N)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper.MiddleSection

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper

/-- The normal middle parabolic's diagonal quotient remains the simple normal
subgroup after adjoining the supplied aligned Sylow subgroup and removing the
intrinsic two-core. The marking is unchanged. -/
theorem sylowAligned_hasBinaryMiddleSection {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G) (e : L ≃* PSL 5)
    (he : SylowAligned L (T : Subgroup G) e) :
    HasBinaryMiddleSection (ambientFlag L (T : Subgroup G) e (middleRoots 5)) := by
  let P := transportedParabolic L e (middleRoots 5)
  let H := ambientFlag L (T : Subgroup G) e (middleRoots 5)
  have hPH : P ≤ H := le_sup_left
  let N := P.subgroupOf H
  let R := (T : Subgroup G).subgroupOf H
  let : N.Normal := transportedParabolic_normal_in_ambientFlag (Or.inr rfl)
    L (T : Subgroup G) e he _ (middleRoots_diagramStable 5)
  let f := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  let a : projectiveParabolic 5 (middleRoots 5) ≃* P :=
    (projectiveParabolic 5 (middleRoots 5)).equivMapOfInjective f hf
  let b : N ≃* projectiveParabolic 5 (middleRoots 5) :=
    (subgroupOfEquivOfLe hPH).trans a.symm
  let q := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hgen : N ⊔ R = ⊤ := by
    change P.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
    rw [← subgroupOf_sup hPH (show (T : Subgroup G) ≤ H from le_sup_right)]
    exact subgroupOf_self H
  exact MiddleSection.hasSection_of_normal N R T.isPGroup'.comap_subtype hgen
    (q.trans MiddleSection.projectiveMiddleQuotientEquiv)

/-- E.1.14(1)'s dimension-five middle flag, under the genuine SQTK source
hypotheses, for exactly the supplied Sylow-aligned marking. -/
theorem sqtk_hasBinaryMiddleSection {G : Type*} [Group G] [Finite G]
    {K : GroupClass} (_hG : IsSQTK K G)
    [IsSimpleGroup (generalizedFitting G)] (T : Sylow 2 G)
    (_hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* PSL 5)
    (he : SylowAligned (generalizedFitting G) (T : Subgroup G) e) :
    HasBinaryMiddleSection
      (ambientFlag (generalizedFitting G) (T : Subgroup G) e (middleRoots 5)) :=
  sylowAligned_hasBinaryMiddleSection (generalizedFitting G) T e he

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.BinaryUpper

end
