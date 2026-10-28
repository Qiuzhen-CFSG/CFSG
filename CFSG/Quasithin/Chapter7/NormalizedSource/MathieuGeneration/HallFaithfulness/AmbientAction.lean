module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.AmbientComponents
public import Theory.GroupAction.NormalizerFixedCentralizer
public import CFSG.Quasithin.ChapterI.Section03.OrdinaryFixedQuotient

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoFour
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M24Table.TwoAKernel
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSOuter.Source
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.SevenExclusion
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport

/-!
# The original cubic pumpup and its literal quotient action

A proper containing two-component yields a nontrivial conjugation action of
the original involution. The simultaneous-centralizer residual transports to
an ordinary fixed component, whose image in the O_{2',2} quotient retains its
M₂₂ central quotient. For nontrivial induced action, actual involution tables
exclude M₂₂, M₂₃, M₂₄, J₄ and HS. Trivial induced action instead identifies the
simple quotient with M₂₂; it does not yet identify the full component.

The Hall consumer constructs these data with the same full J₄ cover, placed
cubic, quotient maps and source hypotheses. Equality of the original residual
with its containing two-component, the pushing-up contradiction and the M₂₄
fixed-line and odd-actor comparisons remain separate source obligations.

Source: Aschbacher--Smith 4.2.13, printed p.612, and 4.4.14,
printed pp.623--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin Sporadic.Mathieu
open CFSG.Quasithin.Chapter4.Section02.RankOneReciprocalEscape
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

/-- A proper containing two-component gives the literal nontrivial involution
on that component and an M₂₂ component in the fixed source-core quotient. -/
theorem proper_m22_twoComponent_action
    {G : Type*} [Group G] [Finite G]
    (t : G) (ht : orderOf t = 2) (D X : Subgroup G)
    (hD : IsComponentIn D (centralizer ({t} : Set G)))
    (eD : (D ⧸ center D) ≃* M22)
    (hX : X.IsTwoComponent) [X.Normal] (hDX : D < X) :
    let a : MulAut X := MulAut.conjNormal t
    orderOf a = 2 ∧
      ∃ B : Subgroup a.fixedSubgroup,
        IsComponent a.fixedSubgroup B ∧ Nonempty (B ≃* D) ∧
        B.map a.fixedSubgroup.subtype = D.subgroupOf X ∧
        IsComponent (MulAut.oddTwoCoreQuotientAut a).fixedSubgroup
          (B.map (MulAut.oddTwoCoreFixedMap a)) ∧
        Nonempty (((B.map (MulAut.oddTwoCoreFixedMap a)) ⧸
          center (B.map (MulAut.oddTwoCoreFixedMap a))) ≃* M22) := by
  let a : MulAut X := MulAut.conjNormal t
  have ha2 : a ^ 2 = 1 := by
    change (MulAut.conjNormal t : MulAut X)^2 = 1
    rw [←map_pow,show t^2=1 from ht ▸ pow_orderOf_eq_one t,map_one]
  have hane : a ≠ 1 := by
    intro he
    have hXC : X ≤ centralizer ({t} : Set G) := by
      intro y hy
      have hh : a ⟨y,hy⟩ = ⟨y,hy⟩ := by rw [he]; rfl
      exact mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)).symm
    have hi := (hD.restrict hDX.le hXC).2.isCComponent
    have hx := (hX.subgroupOf le_rfl).1
    rw [subgroupOf_self] at hx
    exact hDX.not_ge (subgroupOf_eq_top.mp (hi.eq_of_le hx le_top))
  have ha : orderOf a = 2 := orderOf_eq_prime ha2 hane
  let C := X ⊓ centralizer ({t} : Set G)
  have hDC : D ≤ C := le_inf hDX.le hD.1
  let f : a.fixedSubgroup ≃* C :=
    X.normalizerFixedEquivCentralizer ⟨t,by rw [normalizer_eq_top]; exact mem_top t⟩
  let B := (D.subgroupOf C).map f.symm.toMonoidHom
  have hB : IsComponent a.fixedSubgroup B :=
    (hD.restrict hDC inf_le_right).2.map_equiv f.symm
  let e : B ≃* D := (f.symm.subgroupMap (D.subgroupOf C)).symm.trans
    (subgroupOfEquivOfLe hDC)
  have hb : B.map a.fixedSubgroup.subtype = D.subgroupOf X := by
    ext x
    constructor
    · rintro ⟨b,⟨d,hd,rfl⟩,rfl⟩
      exact hd
    · intro hx
      refine ⟨f.symm ⟨x,hDC hx⟩,mem_map_of_mem _ hx,?_⟩
      rfl
  have htop : twoComponentLayer X = ⊤ := by
    have hh := (hX.subgroupOf le_rfl).le_twoComponentLayer
    rw [subgroupOf_self] at hh
    exact top_unique hh
  obtain ⟨hE,⟨eq⟩⟩ := ChapterI.InvolutionSource.fixed_component_oddTwoCore_image htop a ha B hB
  exact ⟨ha,B,hB,⟨e⟩,hb,hE,⟨eq.symm.trans ((centerQuotientCongr e).trans eD)⟩⟩
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open CFSG.Quasithin.Chapter16.OtherPreliminaries

private theorem m22_quotient_card_dvd {B : Type*} [Group B]
    (e : (B ⧸ center B) ≃* M22) : Nat.card M22 ∣ Nat.card B := by
  rw [←Nat.card_congr e.toEquiv]
  exact card_quotient_dvd_card _

private theorem fixed_component_obstruction_congr
    {Q S : Type*} [Group Q] [Group S] (e : Q ≃* S)
    (hex : ∀ (b : MulAut S), orderOf b = 2 →
      ∀ C : Subgroup b.fixedSubgroup, ¬ IsComponent b.fixedSubgroup C)
    (a : MulAut Q) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B) : False := by
  let b := MulAut.congr e a
  let f := MulAut.fixedSubgroupCongr e a
  exact hex b (((MulAut.congr e).orderOf_eq a).trans ha) _ (hB.map_equiv f)

/-- A fixed M₂₂ covering component rules out the M₂₂, M₂₃, M₂₄, J₄ and HS
simple models for a nontrivial involutory automorphism. -/
theorem m22_fixed_component_excludes_large_sporadic
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]
    (a : MulAut Q) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : (B ⧸ center B) ≃* M22) :
    ¬ (Nonempty (Q ≃* M22) ∨ Nonempty (Q ≃* M23) ∨ Nonempty (Q ≃* M24) ∨
      Nonempty (Q ≃* _root_.Janko4.Model) ∨
      Nonempty (Q ≃* _root_.Sporadic.LeechRelated.HS.Carrier)) := by
  have hd := m22_quotient_card_dvd eB
  intro hh
  rcases hh with hh | hh | hh | hh | hh
  all_goals obtain ⟨e⟩ := hh
  · have hle : Nat.card Q ≤ Nat.card a.fixedSubgroup := by
      rw [Nat.card_congr e.toEquiv]
      exact (Nat.le_of_dvd Nat.card_pos hd).trans B.card_le_card_group
    have hf : a.fixedSubgroup = ⊤ := a.fixedSubgroup.eq_top_of_le_card hle
    have he : a = 1 := by
      apply MulEquiv.ext
      intro x
      exact (MulAut.mem_fixedSubgroup _ _).mp (hf ▸ mem_top x)
    rw [he,orderOf_one] at ha
    omega
  · let f := MulAut.fixedSubgroupCongr e a
    have hc := hB.map_equiv f
    exact _root_.Sporadic.Mathieu.M23Geometry.InvolutionCentralizer.fixedSubgroup_no_component_of_inner
      (MulAut.congr e a) (((MulAut.congr e).orderOf_eq a).trans ha)
      (_root_.Sporadic.Mathieu.m23_involution_automorphism_inner _
        (((MulAut.congr e).orderOf_eq a).trans ha)) _ hc
  · let f := MulAut.fixedSubgroupCongr e a
    let C := B.map f.toMonoidHom
    have hc : IsComponent (MulAut.congr e a).fixedSubgroup C := hB.map_equiv f
    rcases (_root_.Sporadic.Mathieu.M24InvolutionCentralizers.fixedSubgroup_alternative
      (MulAut.congr e a) (((MulAut.congr e).orderOf_eq a).trans ha)).2 with hg | hg
    · obtain ⟨g⟩ := hg
      exact Mathieu.m24_twoA_no_component _ (hc.map_equiv g)
    · obtain ⟨g⟩ := hg
      have h7 : 7 ∣ Nat.card B := (by rw [m22_order]; decide : 7 ∣ Nat.card M22).trans hd
      have hc7 : 7 ∣ Nat.card C :=
        (Nat.card_congr (f.subgroupMap B).toEquiv) ▸ h7
      apply _root_.Sporadic.Mathieu.M24InvolutionCentralizers.twoB_centralizer_not_seven
      exact hc7.trans (C.card_subgroup_dvd_card.trans (Nat.card_congr g.toEquiv).dvd)
  · let : IsSimpleGroup _root_.Janko4.Model := e.symm.isSimpleGroup
    let : Group.IsPerfect _root_.Janko4.Model := Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom) e.surjective
    exact fixed_component_obstruction_congr e
      JankoFour.involution_fixed_no_component a ha B hB
  · let : IsSimpleGroup _root_.Sporadic.LeechRelated.HS.Carrier := e.symm.isSimpleGroup
    let : Group.IsPerfect _root_.Sporadic.LeechRelated.HS.Carrier := Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom) e.surjective
    let b := MulAut.congr e a
    let f := MulAut.fixedSubgroupCongr e a
    let C := B.map f.toMonoidHom
    have hc : IsComponent b.fixedSubgroup C := hB.map_equiv f
    have h11 : 11 ∣ Nat.card C := by
      exact (Nat.card_congr (f.subgroupMap B).toEquiv) ▸
        (by rw [m22_order]; decide : 11 ∣ Nat.card M22).trans hd
    by_cases hi : ∃ x,b = MulAut.conj x
    · obtain ⟨g⟩ := JankoTwoHigmanSims.HSInner.inner_component_equiv b
        (((MulAut.congr e).orderOf_eq a).trans ha) hi C hc
      rw [Nat.card_congr g.toEquiv,nat_card_alternatingGroup] at h11
      norm_num at h11
    · obtain ⟨g⟩ := JankoTwoHigmanSims.HSOuter.outer_component_equiv b
        (((MulAut.congr e).orderOf_eq a).trans ha) hi C hc
      rw [Nat.card_congr g.toEquiv,nat_card_alternatingGroup] at h11
      norm_num at h11

/-- If the induced involution is trivial, the same image component exhausts
the simple quotient and identifies it with M₂₂. -/
theorem m22_fixed_component_trivial_action
    {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q] [Group.IsPerfect Q]
    (a : MulAut Q) (ha : a = 1)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eB : (B ⧸ center B) ≃* M22) : Nonempty (Q ≃* M22) := by
  have hz : center Q = ⊥ := Subgroup.center_eq_bot_of_simple_perfect
  let : IsQuasisimple Q := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hf : a.fixedSubgroup = ⊤ := by
    subst a
    ext x
    rw [MulAut.mem_fixedSubgroup]
    simp
  let f : a.fixedSubgroup ≃* Q := (MulEquiv.subgroupCongr hf).trans topEquiv
  have hh := hB.map_equiv f
  have ht : IsComponent Q ⊤ := ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩
  have he : B.map f.toMonoidHom = ⊤ := hh.eq_of_le ht le_top
  let g : B ≃* Q := (f.subgroupMap B).trans ((MulEquiv.subgroupCongr he).trans topEquiv)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans
    ((centerQuotientCongr g.symm).trans eB)⟩
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

/-- The exact quotient action attached to the original local component. The
trivial quotient action is retained separately from equality of subgroups. -/
@[expose] def M22PumpupQuotientActionData {G : Type*} [Group G] [Finite G]
    (t : G) (D X : Subgroup G) : Prop :=
  D = X ∨ ∃ hn : X.Normal,
    let a : MulAut X := @MulAut.conjNormal G _ X hn t
    orderOf a = 2 ∧ ∃ B : Subgroup a.fixedSubgroup,
      IsComponent a.fixedSubgroup B ∧ Nonempty (B ≃* D) ∧
      B.map a.fixedSubgroup.subtype = D.subgroupOf X ∧
      IsComponent (MulAut.oddTwoCoreQuotientAut a).fixedSubgroup
        (B.map (MulAut.oddTwoCoreFixedMap a)) ∧
      Nonempty (((B.map (MulAut.oddTwoCoreFixedMap a)) ⧸
        center (B.map (MulAut.oddTwoCoreFixedMap a))) ≃* M22) ∧
      ((MulAut.oddTwoCoreQuotientAut a = 1 ∧ Nonempty ((X ⧸ oddTwoCore X) ≃* M22)) ∨
        (orderOf (MulAut.oddTwoCoreQuotientAut a) = 2 ∧
          ¬ (Nonempty ((X ⧸ oddTwoCore X) ≃* M22) ∨
            Nonempty ((X ⧸ oddTwoCore X) ≃* M23) ∨
            Nonempty ((X ⧸ oddTwoCore X) ≃* M24) ∨
            Nonempty ((X ⧸ oddTwoCore X) ≃* _root_.Janko4.Model) ∨
            Nonempty ((X ⧸ oddTwoCore X) ≃* _root_.Sporadic.LeechRelated.HS.Carrier))))

/-- The complete action reduction, without assuming faithful quotient action
or identifying the local component with a proper containing two-component. -/
theorem m22_pumpup_quotient_action
    {G : Type*} [Group G] [Finite G]
    (t : G) (ht : orderOf t = 2) (D X : Subgroup G)
    (hD : IsComponentIn D (centralizer ({t} : Set G)))
    (eD : (D ⧸ center D) ≃* M22)
    (hX : X.IsTwoComponent) [X.Normal] (hDX : D ≤ X) :
    M22PumpupQuotientActionData t D X := by
  by_cases he : D = X
  · exact Or.inl he
  right
  refine ⟨inferInstance,?_⟩
  obtain ⟨ha,B,hB,eB,hmap,hE,⟨eE⟩⟩ := proper_m22_twoComponent_action
    t ht D X hD eD hX (lt_of_le_of_ne hDX he)
  refine ⟨ha,B,hB,eB,hmap,hE,⟨eE⟩,?_⟩
  let a : MulAut X := MulAut.conjNormal t
  let b := MulAut.oddTwoCoreQuotientAut a
  let : IsSimpleGroup (X ⧸ oddTwoCore X) := hX.isSimpleGroup_quotient_oddTwoCore
  let := hX.1.perfect
  let : Group.IsPerfect (X ⧸ oddTwoCore X) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  by_cases hb : b = 1
  · exact Or.inl ⟨hb,m22_fixed_component_trivial_action b hb _ hE eE⟩
  · have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
    have hi : Function.Involutive a := fun y => by
      have hh := DFunLike.congr_fun ha2 y
      exact hh
    have hb2 : b ^ 2 = 1 := by
      apply MulEquiv.ext
      intro y
      exact MulAut.oddTwoCoreQuotientAut_involutive a hi y
    have hbo : orderOf b = 2 := orderOf_eq_prime hb2 hb
    exact Or.inr ⟨hbo,m22_fixed_component_excludes_large_sporadic b hbo _ hE eE⟩

/-- The simultaneous-centralizer ordinary component, viewed inside C_G(x). -/
private theorem simultaneous_component_subgroupOf
    {G : Type*} [Group G] (x r : G) (hrx : r ∈ centralizer ({x} : Set G))
    (S : Subgroup G)
    (hS : IsComponentIn S (centralizer ({x} : Set G) ⊓ centralizer ({r} : Set G))) :
    IsComponentIn (S.subgroupOf (centralizer ({x} : Set G)))
      (centralizer ({(⟨r,hrx⟩ : centralizer ({x} : Set G))} : Set (centralizer ({x} : Set G)))) := by
  let Cx := centralizer ({x} : Set G)
  let C := centralizer ({(⟨r,hrx⟩ : Cx)} : Set Cx)
  let Cr := centralizer ({x} : Set G) ⊓ centralizer ({r} : Set G)
  let D := S.subgroupOf Cx
  have hSCx : S ≤ Cx := hS.1.trans inf_le_left
  have hDC : D ≤ C := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp (hS.1 hs).2))
  let f : C →* Cr := (Cx.subtype.comp C.subtype).codRestrict Cr (fun c =>
    ⟨c.val.property,mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp c.property))⟩)
  let e : (D.subgroupOf C) ≃* S :=
    (subgroupOfEquivOfLe hDC).trans (subgroupOfEquivOfLe hSCx)
  let := hS.quasisimple
  exact ⟨hDC,hS.2.1.comap f,IsQuasisimple.of_mulEquiv e.symm⟩

/-- The literal cubic residual and the conjugation action on its original
odd-E closure inside the full cubic centralizer. -/
@[expose] def CubicPumpupQuotientAction {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) (r : G) : Prop :=
  ∃ hrx : r ∈ centralizer ({((x : H) : G)} : Set G),
    let Cx := centralizer ({((x : H) : G)} : Set G)
    let D := (cubicResidualImage H K x).subgroupOf Cx
    M22PumpupQuotientActionData (⟨r,hrx⟩ : Cx) D (componentOrbit D (oddELayer Cx))

/-- Construct the original residual's quotient action from the already proved
ambient placement. Every subgroup map is the original literal inclusion. -/
theorem cubic_pumpup_quotient_action {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) (r : G) (hr : orderOf r = 2)
    (hp : CubicPumpupData H K x r)
    (hS : IsComponentIn (cubicResidualImage H K x)
      (centralizer ({((x : H) : G)} : Set G) ⊓ centralizer ({r} : Set G)))
    (eS : (solvableResidual (centralizer ({x} : Set K)) ⧸
      center (solvableResidual (centralizer ({x} : Set K)))) ≃* M22) :
    CubicPumpupQuotientAction H K x r := by
  obtain ⟨hrx,hX,hn,_,hle,_,_⟩ := hp
  let Cx := centralizer ({((x : H) : G)} : Set G)
  let S := cubicResidualImage H K x
  let D := S.subgroupOf Cx
  let X := componentOrbit D (oddELayer Cx)
  let := hn
  let a : solvableResidual (centralizer ({x} : Set K)) ≃* S :=
    ((solvableResidual (centralizer ({x} : Set K))).equivMapOfInjective
      (centralizer ({x} : Set K)).subtype
      (centralizer ({x} : Set K)).subtype_injective).trans
      (((solvableResidual (centralizer ({x} : Set K))).map
        (centralizer ({x} : Set K)).subtype).equivMapOfInjective
          (H.subtype.comp K.subtype) (H.subtype_injective.comp K.subtype_injective))
  let e : D ≃* solvableResidual (centralizer ({x} : Set K)) :=
    (subgroupOfEquivOfLe (hS.1.trans inf_le_left)).trans a.symm
  refine ⟨hrx,?_⟩
  exact m22_pumpup_quotient_action (⟨r,hrx⟩ : Cx) ((orderOf_coe _).symm.trans hr)
    D X (simultaneous_component_subgroupOf _ r hrx S hS)
    ((centerQuotientCongr e).trans eS) hX hle
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Janko4.InvolutionCentralizers

/-- The full source configuration, retaining the original residual and all
maps together with the induced quotient-action comparison. -/
@[expose] def MathieuPushingUpQuotientActionCase {G : Type*} [Group G] [Finite G]
    (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (r : H.pCoreIn 2) (H₁ : Subgroup G), orderOf r = 2 ∧
        centralizer ({(r : G)} : Set G) ≤ H₁ ∧
        IsComponentIn (K.map H.subtype) H₁ ∧
        ((K.map H.subtype).subgroupOf H₁).Normal ∧
        IsComponentIn (K.map H.subtype) (centralizer ({(r : G)} : Set G)) ∧
      ∃ e : (K ⧸ center K) ≃* Janko4.Model,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
        let R := First.centralizer.comap q
        ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
          (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({x} : Set R)) ∈
            solvableResidual (Subgroup.centralizer ({x} : Set R)) ∧
          solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)) =
            (solvableResidual (Subgroup.centralizer ({x} : Set R))).map
              (R.subtype.elementCentralizerMap x) ∧
          IsQuasisimple (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ∧
          Nonempty (((solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ⧸
            center (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)))) ≃* M22) ∧
          (∃ g : K, ((g * (x : K) * g⁻¹ : K) : H) ∈ F.subgroupOf H ∧
            let y := g * (x : K) * g⁻¹
            IsQuasisimple (solvableResidual (centralizer ({y} : Set K))) ∧
              Nonempty ((solvableResidual (centralizer ({y} : Set K)) ⧸
                center (solvableResidual (centralizer ({y} : Set K)))) ≃* M22) ∧
              CubicAmbientData H K y ∧
              (let C := centralizer ({((y : H) : G)} : Set G) ⊓ centralizer ({(r : G)} : Set G)
               IsComponentIn (cubicResidualImage H K y) C ∧
                 ((cubicResidualImage H K y).subgroupOf C).Normal) ∧
              CubicPumpupData H K y (r : G) ∧
              CubicPumpupQuotientAction H K y (r : G) ∧
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))


/-- Add the quotient action on the unique containing two-component, using the
same full J₄ cover, placed cubic and reselected involution. -/
theorem pushingUp_cubic_quotient_action {G : Type*} [Group G] [Finite G]
    {L V A : Subgroup G} (hc : MathieuPushingUpAmbientComponentCase L V A) :
    MathieuPushingUpQuotientActionCase L V A := by
  obtain ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,huy⟩,hux⟩ := hc
  have hact := cubic_pumpup_quotient_action H K (g * (x : K) * g⁻¹) (r : G)
    ((orderOf_coe r).trans hr) hp hs.1 hey.some
  exact ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,huy⟩,hux⟩
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

set_option maxHeartbeats 400000 in
/-- The literal Hall obstruction constructs the actual involution action and
fixed M₂₂ quotient component on the original cubic pumpup. The full cover,
quotient maps and Hall hypotheses are retained, with no extra premise. -/
theorem sourceOrbit_mathieu_hall_quotient_action_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (MathieuPushingUpQuotientActionCase L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  obtain ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,hcase⟩ :=
    @sourceOrbit_mathieu_hall_ambient_component_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  exact ⟨p,A,hp,ho,hne,he,hAH,hAC,hAV,hAT,hout,hclosure,hcompare,
    hcase.imp pushingUp_cubic_quotient_action id⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
