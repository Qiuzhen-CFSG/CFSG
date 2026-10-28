module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoFrameProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoTensorApplication

/-!
# One aligned Hall–Janko frame in the original mixed tensor pair

The same reduced endpoint frame and the same original outer involution
satisfy all three d-, z-, and k-action relations and the order-eight xq
relation in the literal H/AT/BT configuration. The same frame also has order six
for xt in the literal H/O₂(H) quotient. The full original Borel
and both original endpoint supplements are retained. The reduced comparison
is a compatible amalgam isomorphism, with both overlap squares.

Source: DGS (15.3), printed pp.229–230, used in the original
Aschbacher–Smith F.1.11–12 tensor configuration. The order-twelve product in the original group,
marked Aut(J₂) comparison and unconditional reduced recognition remain open.
-/

public section
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory Chapter3.Section02 MixedZeroCore
open ChapterF.Source ChapterF.Source.DGS85.OriginalExtension ChapterF.GreenBook
open SuzukiContainment
private theorem quotient_order_subgroupCongr {G : Type*} [Group G]
    (P H : Subgroup G) (he : P=H) (a b : P) :
    orderOf (QuotientGroup.mk' (pCore 2 H)
      (MulEquiv.subgroupCongr he a*MulEquiv.subgroupCongr he b))=
        orderOf (QuotientGroup.mk' (pCore 2 P) (a*b)) := by
  subst H
  rfl

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}

/-- The frame's own q has the order-eight product with the same involution
that fixes its d and z and inverts its k in the original full BT. -/
theorem mixed_cubic_factor_aligned_frame_product_of_reduced_j2
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A B U : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hBA : B ≤ A) (hBK : B ≤ (pResidual 2 H).map H.subtype) (hB3 : Nat.card B = 3)
    (hU : CubicFactor T A B U) (hzero : pCore 2 (H ⊔ A : Subgroup G) = ⊥)
    (e : RankTwoAmalgam.Iso
      (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G))
      HallJanko.j2Model.toMarking.amalgam)
    (hne : (T : Subgroup G) ≠ SuzukiContainment.reducedSylow
      ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) :
    ∃ F : JankoTwo.GeneratorRelations.Frame
      (reducedAmalgam ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)),
      ∃ x t : H, (t:G)=(F.t:G) ∧ (x:G)∈B ⊔ (T : Subgroup G) ∧ x^2=1 ∧
      (x:G)∉commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ∧
      F.k*F.z=F.z*F.k ∧ (x:G)*(F.k:G)*(x:G)⁻¹=(F.k:G)⁻¹ ∧
      (x:G)*(F.d:G)=(F.d:G)*(x:G) ∧ (x:G)*(F.z:G)=(F.z:G)*(x:G) ∧
      orderOf ((x:G)*(F.q:G))=8 ∧
      orderOf (QuotientGroup.mk' (pCore 2 H) (x*t))=6 ∧
      commonBorel ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) ⊔ zpowers (x:G)=B ⊔ (T : Subgroup G) ∧
      parabolic ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 0 ⊔ zpowers (x:G)=H ∧
      parabolic ![(pResidual 2 H).map H.subtype,U]
        (twoCore (B ⊔ (T : Subgroup G) : Subgroup G)) 1 ⊔ zpowers (x:G)=A ⊔ (T : Subgroup G) := by
  obtain ⟨hf,_,_,_,hb,hp,hAT⟩ :=
    mixed_cubic_factor_rank_two hH eK A B U hAB hBA hBK hB3 hU hzero
  obtain ⟨F,x,_,hkz,hx,hxN,hxk,hxd,hxz,hxq,h6,hB,hP⟩ :=
    JankoTwo.original_aligned_frame_product hf 0 1 e hne
  have hBsup := congrArg (Subgroup.map (commonBorel _ _).subtype) hB.sup_eq_top
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (reduced_commonBorel_le hf),
    MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hBsup
  change commonBorel ![(pResidual 2 H).map H.subtype,U]
      (reducedSylow ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) ⊔
        zpowers (x:G)=commonBorel ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) at hBsup
  have hPsup (r : Fin 2) := congrArg (Subgroup.map (parabolic _ _ r).subtype) (hP r).sup_eq_top
  have hPg (r : Fin 2) :
      parabolic ![(pResidual 2 H).map H.subtype,U]
        (SuzukiContainment.reducedSylow ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G)) r ⊔
          zpowers (x:G)=parabolic ![(pResidual 2 H).map H.subtype,U] (T : Subgroup G) r := by
    have hh := hPsup r
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (reduced_parabolic_le hf r),
      MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  let a := MulEquiv.subgroupCongr hp
  let xP := inclusion (commonBorel_le_parabolic (L:=![(pResidual 2 H).map H.subtype,U]) 0) x
  let tP := inclusion (reduced_parabolic_le hf 0) F.t
  have hxP : xP^2=1 := by
    simpa only [map_pow,map_one] using congrArg
      (inclusion (commonBorel_le_parabolic (L:=![(pResidual 2 H).map H.subtype,U]) 0)) hx
  have h6' : orderOf (QuotientGroup.mk' (pCore 2 H) (a xP*a tP))=6 := by
    rw [quotient_order_subgroupCongr]
    exact h6
  have hax : (a xP:G)=(x:G) := rfl
  refine ⟨F,a xP,a tP,rfl,?_,?_,?_,hkz,hxk,hxd,hxz,hxq,h6',?_,?_,?_⟩
  · exact hb ▸ x.property
  · rw [←map_pow,hxP,map_one]
  · rw [hax]
    simpa only [SuzukiContainment.reducedSylow,hb] using hxN
  · rw [hax]
    simpa only [SuzukiContainment.reducedSylow,hb] using hBsup
  · rw [hax]
    simpa only [SuzukiContainment.reducedSylow,hb,hp] using hPg 0
  · rw [hax]
    simpa only [SuzukiContainment.reducedSylow,hb,hAT] using hPg 1

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
