module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoProductLift
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoTensorApplication

/-!
# The order-twelve lift in the literal mixed tensor endpoint

The marked reduced comparison and the original Borel actor give the
nontrivial central sixth power in H. Thus order six in the actual H/O₂(H)
quotient gives order twelve in H. Both reduced endpoint maps and the full
BT are retained. The actor marking and quotient-order premise are explicit;
this theorem does not construct an Aut(J₂) comparison or discharge reduced
recognition.

Source: DGS (15.3), printed pp.230–231, applied to the original
Aschbacher–Smith F.1.11–12 mixed tensor configuration.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Chapter3.Section02 MixedZeroCore
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension ChapterF.GreenBook
open SuzukiContainment JankoTwo.ProductLift

private theorem quotient_order_congr {G : Type*} [Group G]
    (P H : Subgroup G) (he : P=H) (a : P) :
    orderOf (QuotientGroup.mk' (pCore 2 H) (MulEquiv.subgroupCongr he a))=
      orderOf (QuotientGroup.mk' (pCore 2 P) a) := by
  subst H
  rfl

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The central lift is in the original H, with the literal H/O₂(H)
quotient and full BT. The displayed actor equations are the three markings
used by the paired-endpoint lifting theorem. -/
theorem mixed_cubic_factor_product_twelve_of_marked_actor
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    (e : RankTwoAmalgam.Iso
      (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) HallJanko.j2Model.toMarking.amalgam)
    (x t : H) (hxB : (x:G)∈B ⊔ (T : Subgroup G)) (hx : x^2=1)
    (ht : (t:G)=(e.left.symm (catalogueIso.left sourceInverter):G))
    (hk : (x:G)*(e.middle.symm (catalogueIso.middle sourceCartan):G)*(x:G)⁻¹=(e.middle.symm (catalogueIso.middle sourceCartan):G)⁻¹)
    (hd : (x:G)*(e.right.symm (catalogueIso.right sourceCubic):G)=(e.right.symm (catalogueIso.right sourceCubic):G)*(x:G))
    (hz : (x:G)*(e.middle.symm (catalogueIso.middle sourceCentral):G)=(e.middle.symm (catalogueIso.middle sourceCentral):G)*(x:G))
    (h6 : orderOf (QuotientGroup.mk' (pCore 2 H) (x*t))=6) : orderOf (x*t)=12 := by
  obtain ⟨hf,_,_,_,hb,hp,_⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  let f := e.trans catalogueIso.symm
  let y : commonBorel ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) :=
    ⟨x,hb.symm ▸ hxB⟩
  have hy : y^2=1 := Subtype.ext (congrArg (fun z : H => (z:G)) hx)
  let P := parabolic ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) 0
  let a : P := inclusion (commonBorel_le_parabolic 0) y*
    inclusion (reduced_parabolic_le hf 0) (e.left.symm (catalogueIso.left sourceInverter))
  have ha : MulEquiv.subgroupCongr hp a=x*t := by
    apply Subtype.ext
    change (x:G)*(e.left.symm (catalogueIso.left sourceInverter):G)=(x:G)*(t:G)
    rw [ht]
  have h6' : orderOf (QuotientGroup.mk' (pCore 2 P) a)=6 := by
    rw [←quotient_order_congr P H hp a,ha]
    exact h6
  have ho := original_product_twelve hf 0 1 f y hy hk hd hz h6'
  change orderOf ((x:G)*(e.left.symm (catalogueIso.left sourceInverter):G))=12 at ho
  rw [←ht] at ho
  exact (orderOf_coe (x*t)).symm.trans ho

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
