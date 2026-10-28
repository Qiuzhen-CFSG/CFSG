module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.RootOrbit
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import GorensteinWalter.PSL2PerfectOfCard
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.ModuleLift
public import Theory.GroupTheory.PPerfectHom

/-!
# The single short residual of the original root-pair overgroup

In the root-image branch the original V-action gives a surjection from
IQ₁ to the marked SL₂ over the nonbinary field, with two-group kernel.
Every short block in C.1.27 has nontrivial image: otherwise its two-perfect
property would make it trivial. Subnormality and simplicity make each
image the entire SL₂. Distinct commuting blocks would therefore make SL₂
abelian, so the residual orbit has exactly one member. Thus O²(IQ₁) is an
actual chi-zero block, with its original ambient embedding.

The normal chosen V contains this short residual’s intrinsic moved layer.
Thus the residual centralizes O₂(L)/V. Its nontrivial image in the simple
symplectic quotient and perfectness of L propagate this centralization to
all of L. The genuine multiplier identity then gives O₂(L)=V. This handles
the root-image branch without treating C.1.29’s block alternative as a
characteristic-subgroup conclusion. The full-image classification remains
with qt-d-1222-natural-closure-sp4 and its nonbinary MS prerequisite.
Source: Aschbacher--Smith 11.5.7, p.783, and C.1.27--29, pp.133--134.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open RadicalAction

private theorem short_image_ne_bot {H A : Type*} [Group H] [Group A]
    (q : H →* A) (hk : IsPGroup 2 q.ker)
    (B : Subgroup H) (hb : ChapterC.IsShort B) : B.map q ≠ ⊥ := by
  intro he
  have hBker : B ≤ q.ker := by
    intro b hb
    exact MonoidHom.mem_ker.mpr
      (show q b = 1 from (he ▸ mem_map_of_mem q hb : q b ∈ (⊥ : Subgroup A)))
  have hpB : IsPGroup 2 B := hk.to_le hBker
  have heB : (⊥ : Subgroup B) = ⊤ :=
    hb.twoPerfect ⊥ inferInstance (hpB.of_equiv (QuotientGroup.quotientBot).symm)
  exact hb.blockU_ne_bot (bot_unique ((le_top : ChapterC.blockU B ≤ ⊤).trans_eq heB.symm))

private theorem residual_block_of_simple_quotient
    {H A : Type*} [Group H] [Finite H] [Group A]
    [IsSimpleGroup A] [Group.IsPerfect A]
    (q : H →* A) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (S : Sylow 2 H) (ho : RootResidualOrbit S) :
    ChapterC.IsChiZeroBlockIn (pResidual 2 H) := by
  obtain ⟨F,hF,hblocks,hgen,hcomm,_⟩ := ho
  obtain ⟨B,hB⟩ := hF
  have himage (K : Subgroup H) (hK : K ∈ F) : K.map q = ⊤ :=
    (Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup
      (inferInstance : IsSimpleGroup A)
      (Subgroup.IsSubnormal.map hq (hblocks K hK).1.subnormal)).resolve_left
        (short_image_ne_bot q hk K (hblocks K hK).1.short)
  have hone (K : Subgroup H) (hK : K ∈ F) : K = B := by
    by_contra hne
    have hc := congrArg (Subgroup.map q) (hcomm hK hB hne)
    rw [map_commutator,himage K hK,himage B hB,Subgroup.map_bot] at hc
    change _root_.commutator A = ⊥ at hc
    rw [Group.IsPerfect.commutator_eq_top] at hc
    exact top_ne_bot hc
  have he : pResidual 2 H = B := by
    rw [←hgen]
    apply le_antisymm (sSup_le fun K hK => (hone K hK).le) (le_sSup hB)
  rw [he]
  exact hblocks B hB

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The literal opposite-pair action supplies the simple quotient and a
 two-group kernel; it is not an unrelated abstract SL₂ model. -/
theorem root_case_quotient_of_kernel (m : MarkedFlag E)
    (hW : E.W ≤ E.G₁.pCoreIn 2) {y : G} (hy : y ∈ L)
    (g : Sp E.input.field.Carrier)
    (hpair : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hrootW : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hkernel : centralizer (V : Set G) ⊓ (L ⊔ E.G₁.pCoreIn 2) ≤ E.G₁.pCoreIn 2) :
    ∃ q : (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2 : Subgroup G) →*
        Matrix.SpecialLinearGroup (Fin 2) E.input.field.Carrier,
      Function.Surjective q ∧ IsPGroup 2 q.ker ∧
        q.ker = (centralizer (V : Set G)).subgroupOf
          (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2) := by
  let I := oppositeJoin (auxiliaryW E) y
  let Q := E.G₁.pCoreIn 2
  let J := I ⊔ Q
  have hJL : J ≤ L ⊔ Q := sup_le (opposite_join_le_core_join E hW hy) le_sup_right
  have hQN : Q ≤ normalizer (V : Set G) := (core_le_sylow E m).trans E.input.sylow_normalizes
  have hJN : J ≤ normalizer (V : Set G) := hJL.trans (sup_le D.normalizes hQN)
  let f : J →* MulAut V := V.normalizerMonoidHom.comp (inclusion hJN)
  have hJimage : actionImage (V := V) J = actionImage (V := V) I := by
    change ((I ⊔ Q).subgroupOf (normalizer (V : Set G))).map V.normalizerMonoidHom = _
    rw [subgroupOf_sup (le_sup_left.trans hJN) hQN,Subgroup.map_sup]
    change actionImage (V := V) I ⊔ actionImage (V := V) Q = _
    apply sup_eq_left.mpr
    rw [hroot,←hrootW]
    exact Terminal.actionImage_mono le_sup_left
  have hrange : f.range = actionImage (V := V) I := by
    rw [←hJimage]
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,hJN x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
  let e := (MulEquiv.subgroupCongr hrange).trans
    (OppositeGeometry.markedPairImageEquiv E m g hpair)
  let q := e.toMonoidHom.comp f.rangeRestrict
  have hker : q.ker = (centralizer (V : Set G)).subgroupOf J := by
    ext x
    change e (f.rangeRestrict x) = 1 ↔ (x : G) ∈ centralizer (V : Set G)
    constructor
    · intro hx
      have hx0 : f x = 1 := congrArg Subtype.val (e.injective (hx.trans e.map_one.symm))
      change V.normalizerMonoidHom (inclusion hJN x) = 1 at hx0
      rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker] at hx0
      exact hx0
    · intro hx
      have hx0 : f x = 1 := by
        change V.normalizerMonoidHom (inclusion hJN x) = 1
        rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker]
        exact hx
      have hh : f.rangeRestrict x = 1 := Subtype.ext hx0
      rw [hh,e.map_one]
  refine ⟨q,e.surjective.comp f.rangeRestrict_surjective,?_,hker⟩
  apply (isPGroup_pCoreIn 2 E.G₁).comap_subtype.to_le
  rw [hker]
  exact fun x hx => hkernel ⟨hx,hJL x.property⟩

/-- The C.1.27 orbit in the specified original opposite pair is a single
chi-zero block, retaining the chosen Cartan-compatible pair. -/
theorem root_case_residual_block_of_pair (m : MarkedFlag E)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hV : V ≤ E.G₁.pCoreIn 2) (hW : E.W ≤ E.G₁.pCoreIn 2)
    {y : G} (hy : y ∈ L) (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hpair : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hrootW : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hkernel : centralizer (V : Set G) ⊓ (L ⊔ E.G₁.pCoreIn 2) ≤ E.G₁.pCoreIn 2) :
    ChapterC.IsChiZeroBlockIn
      (pResidual 2 (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2 : Subgroup G)) := by
  obtain ⟨S,_,_,ho⟩ := root_case_residual_orbit_of_pair E m hout hV hW hy g hlocal
    hpair hrootW hroot hkernel
  obtain ⟨q,hq,hk,_⟩ := root_case_quotient_of_kernel E m hW hy g hpair hrootW hroot hkernel
  have hF : 4 ≤ Nat.card E.input.field.Carrier := by
    rw [E.input.field.card_eq]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) E.input.nonbinary
  let e := Theory.PSL2.sl2QuotientEquiv E.input.field.Carrier
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E.input.field.Carrier) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) E.input.field.Carrier) := e.isSimpleGroup
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E.input.field.Carrier) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three E.input.field.Carrier (by omega)
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) E.input.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact residual_block_of_simple_quotient q hq hk S ho

/-- The actual short residual controls the original core commutator through
the original chosen module, including its central fixed part. -/
theorem root_case_core_commutator_le_seed_of_pair (m : MarkedFlag E)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hV : V ≤ E.G₁.pCoreIn 2) (hW : E.W ≤ E.G₁.pCoreIn 2)
    {y : G} (hy : y ∈ L) (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hpair : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hrootW : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hkernel : centralizer (V : Set G) ⊓ (L ⊔ E.G₁.pCoreIn 2) ≤ E.G₁.pCoreIn 2)
    (hcore : L.pCoreIn 2 ≤ E.G₁.pCoreIn 2) :
    ⁅L.pCoreIn 2,
      (pResidual 2 (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2 : Subgroup G)).map
        (oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2).subtype⁆ ≤ V := by
  let J := oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2
  let B := pResidual 2 J
  let A := V.subgroupOf J
  let P := (L.pCoreIn 2).subgroupOf J
  have hb : ChapterC.IsChiZeroBlockIn B := root_case_residual_block_of_pair E m hout
    hV hW hy g hlocal hpair hrootW hroot hkernel
  obtain ⟨q,_,hk,hker⟩ := root_case_quotient_of_kernel E m hW hy g hpair hrootW hroot hkernel
  have hJL : J ≤ L ⊔ E.G₁.pCoreIn 2 :=
    sup_le (opposite_join_le_core_join E hW hy) le_sup_right
  have hJN : J ≤ normalizer (V : Set G) := hJL.trans
    (sup_le D.normalizes ((core_le_sylow E m).trans E.input.sylow_normalizes))
  have hJR : J ≤ normalizer (L.pCoreIn 2 : Set G) :=
    (hJL.trans (sup_le L.le_normalizer
      ((core_le_sylow E m).trans D.sylow_normalizes_component))).trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  let : A.Normal := normal_subgroupOf_of_le_normalizer hJN
  let : P.Normal := normal_subgroupOf_of_le_normalizer hJR
  have hAp : IsPGroup 2 A := by
    let := D.elementary
    exact (IsElementaryAbelian.isPGroup 2 V).comap_subtype
  have hAnot : ¬ B ≤ centralizer (A : Set J) := by
    intro hc
    apply short_image_ne_bot q hk B hb.1.short
    apply (Subgroup.map_eq_bot_iff B).mpr
    rw [hker]
    intro b hb v hv
    exact congrArg Subtype.val (hc hb (⟨v,mem_sup_right (hV hv)⟩ : J) hv)
  have hU : (ChapterC.blockU B).map B.subtype ≤ A :=
    (ChapterC.RankOne.ChiProduct.normal_two_layer_short_dichotomy B A hb.1.short hAp
      (commutator_le_core_commutator_of_isSubnormal B A hb.1.subnormal
        hb.1.short.twoPerfect hAp le_normalizer_of_normal)).resolve_right hAnot
  have hc : ⁅P,B⁆ ≤ A :=
    (commutator_le_core_commutator_of_isSubnormal B P hb.1.subnormal
      hb.1.short.twoPerfect (isPGroup_pCoreIn 2 L).comap_subtype
      le_normalizer_of_normal).trans hU
  have hm := Subgroup.map_mono (f := J.subtype) hc
  rw [map_commutator,
    map_subgroupOf_eq_of_le (hcore.trans (show E.G₁.pCoreIn 2 ≤ J from le_sup_right)),
    map_subgroupOf_eq_of_le (hV.trans (show E.G₁.pCoreIn 2 ≤ J from le_sup_right))] at hm
  exact hm

private theorem core_eq_of_moving_residual (m : MarkedFlag E)
    (B : Subgroup G) (hBL : B ≤ L) (hBnot : ¬ B ≤ L.pCoreIn 2)
    (hcomm : ⁅L.pCoreIn 2,B⁆ ≤ V) : L.pCoreIn 2 = V := by
  let R := L.pCoreIn 2
  let N := commutatorPreimage L R V
  have hNL : N ≤ L := commutatorPreimage_le L R V
  have hLR : L ≤ normalizer (R : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hLN : L ≤ normalizer (N : Set G) :=
    commutatorPreimage_normalized L R V L D.normalizes L.le_normalizer hLR D.normalizes
  have hBN : B ≤ N := le_commutatorPreimage hBL (by rwa [commutator_comm])
  let N' := N.subgroupOf L
  let : N'.Normal := normal_subgroupOf_of_le_normalizer hLN
  let q := m.action.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.action.groupEquiv.surjective.comp
    (QuotientGroup.mk'_surjective (pCore 2 L))
  have hk : q.ker = pCore 2 L := by
    ext x
    change m.action.groupEquiv (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
    rw [m.action.groupEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hF : 3 < Nat.card E.input.field.Carrier := by
    rw [E.input.field.card_eq]
    exact lt_of_lt_of_le (by decide : 3 < 2^2)
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) E.input.nonbinary)
  let : IsSimpleGroup ((Sp E.input.field.Carrier) ⧸ center (Sp E.input.field.Carrier)) :=
    SimpleQuotients.isSimpleGroup hF
  let : IsSimpleGroup (Sp E.input.field.Carrier) := EvenProjective.equiv.isSimpleGroup
  have himage : N'.map q = ⊤ := by
    apply ((inferInstance : N'.Normal).map q hq).eq_bot_or_eq_top.resolve_left
    intro hz
    have hNk : N' ≤ pCore 2 L := by
      rw [←hk]
      exact (Subgroup.map_eq_bot_iff N').mp hz
    apply hBnot
    have hh := Subgroup.map_mono (f := L.subtype) hNk
    rw [map_subgroupOf_eq_of_le hNL] at hh
    exact hBN.trans hh
  have hgen : N' ⊔ pCore 2 L = ⊤ := by
    have hh := congrArg (Subgroup.comap q) himage
    simpa only [comap_map_eq,comap_top,hk] using hh
  have hp : IsPGroup 2 (L ⧸ N') :=
    isPGroup_quotient_of_sup_eq_top N' (pCore 2 L) pCore_isPGroup hgen
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect E.input.source.maximal_faithful.1.1
  have hNtop : N' = ⊤ := by
    by_contra hn
    let : Nontrivial (L ⧸ N') := QuotientGroup.nontrivial_iff.mpr hn
    exact Group.IsPerfect.not_isNilpotent (L ⧸ N') hp.isNilpotent
  have he : N = L := by
    have hh := congrArg (Subgroup.map L.subtype) hNtop
    simpa only [N',map_subgroupOf_eq_of_le hNL,←MonoidHom.range_eq_map,range_subtype] using hh
  have hc : ⁅L,R⁆ ≤ V := by
    rw [←he]
    exact commutator_commutatorPreimage_le L R V D.normalizes
  apply le_antisymm _ D.le_componentCore
  rw [core_eq_commutator E m,commutator_comm]
  exact hc

/-- The simple original symplectic quotient propagates the single short
residual bound to the whole original core. -/
theorem root_case_core_eq_seed_of_pair (m : MarkedFlag E)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hV : V ≤ E.G₁.pCoreIn 2) (hW : E.W ≤ E.G₁.pCoreIn 2)
    {y : G} (hy : y ∈ L) (g : Sp E.input.field.Carrier)
    (hlocal : PointModel.image m E.L₁ = pointLocal.map (MulAut.conj g).toMonoidHom)
    (hpair : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) =
      (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m))
    (hrootW : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hkernel : centralizer (V : Set G) ⊓ (L ⊔ E.G₁.pCoreIn 2) ≤ E.G₁.pCoreIn 2)
    (hcore : L.pCoreIn 2 ≤ E.G₁.pCoreIn 2) : L.pCoreIn 2 = V := by
  let J := oppositeJoin (auxiliaryW E) y ⊔ E.G₁.pCoreIn 2
  let B := pResidual 2 J
  have hJL : J ≤ L ⊔ E.G₁.pCoreIn 2 :=
    sup_le (opposite_join_le_core_join E hW hy) le_sup_right
  have hJN : J ≤ normalizer (L : Set G) := hJL.trans
    (sup_le L.le_normalizer ((core_le_sylow E m).trans D.sylow_normalizes_component))
  let N := L.subgroupOf J
  let Q := (E.G₁.pCoreIn 2).subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer hJN
  have hgen : N ⊔ Q = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨l,hl,q,hq,he⟩ := core_join_product E m x (hJL x.property)
    have hqJ : q ∈ J := mem_sup_right hq
    have hlJ : l ∈ J := by
      have hh := J.mul_mem x.property (J.inv_mem hqJ)
      rw [←he,mul_inv_cancel_right] at hh
      exact hh
    have he' : (⟨l,hlJ⟩ : J) * ⟨q,hqJ⟩ = x := Subtype.ext he
    rw [←he']
    exact mul_mem (mem_sup_left hl) (mem_sup_right hq)
  have hBN : B ≤ N := sInf_le ⟨inferInstance,
    isPGroup_quotient_of_sup_eq_top N Q (isPGroup_pCoreIn 2 E.G₁).comap_subtype hgen⟩
  have hBL : B.map J.subtype ≤ L := by
    rintro _ ⟨b,hb,rfl⟩
    exact hBN hb
  have hb : ChapterC.IsChiZeroBlockIn B := root_case_residual_block_of_pair E m hout
    hV hW hy g hlocal hpair hrootW hroot hkernel
  obtain ⟨q,_,hk,hker⟩ := root_case_quotient_of_kernel E m hW hy g hpair hrootW hroot hkernel
  have hRc : L.pCoreIn 2 ≤ centralizer (V : Set G) := by
    rintro _ ⟨r,hr,rfl⟩
    have hh : FullAction.componentHom (D := D) r = 1 :=
      (FullAction.componentHom_ker E).ge hr
    change V.normalizerMonoidHom (inclusion D.normalizes r) = 1 at hh
    rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker] at hh
    exact hh
  have hBnot : ¬ B.map J.subtype ≤ L.pCoreIn 2 := by
    intro hc
    apply short_image_ne_bot q hk B hb.1.short
    apply (Subgroup.map_eq_bot_iff B).mpr
    rw [hker]
    intro b hb
    exact hRc (hc (mem_map_of_mem J.subtype hb))
  exact core_eq_of_moving_residual E m (B.map J.subtype) hBL hBnot
    (root_case_core_commutator_le_seed_of_pair E m hout hV hW hy g hlocal hpair
      hrootW hroot hkernel hcore)

/-- Source application: the root-image branch identifies the original core
with the chosen seed, without a symplectic block premise. -/
theorem root_case_core_eq_seed_of_preceding (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hn3 : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (hti : ∀ x ∈ E.M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) (hVX : ⁅V,E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hne : ¬ IsMulCommutative E.W)
    (hroot : actionImage (V := V) (E.G₁.pCoreIn 2) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype) : L.pCoreIn 2 = V := by
  have hXL : E.X ≤ L := hX.1.trans inf_le_left
  have hXG : E.X ≤ E.G₁ := by
    change E.X ≤ normalizer (E.V₁ : Set G)
    rw [m.point_preimage]
    exact OppositeGeometry.cartan_normalizes_marked_flag E m hX 0
  obtain ⟨hV,hW,_,hrootW,hmove,_,hPhi,_⟩ :=
    RadicalAction.initial_branch_of_preceding E m g hpoint hthree hcartan hXL hXG
      hn3 hirr hti hgen hVX hfour hfive hne
  have hcore := NaturalQuotient.core_le_point_core E m hX hV hW hrootW hmove hPhi
    hfour hfive hti (CoverGeometry.radical_commutator m g hpoint hthree) hgen
  have hkernel := core_join_action_kernel_of_root_image E m g hpoint hcartan hXL hXG hcore hroot
  obtain ⟨g',y,_,hlocal,_,hpair,_⟩ :=
    OppositeGeometry.exists_opposite_pair_geometry E m hW hrootW hPhi
  exact root_case_core_eq_seed_of_pair E m hout hV hW y.property g' hlocal hpair
    hrootW hroot hkernel hcore

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
