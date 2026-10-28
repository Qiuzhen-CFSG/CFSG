module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ShortUniqueFixed
public import CFSG.Quasithin.ChapterI.Section06To08.UniqueFixedSource
public import Theory.SpecificGroups.Triality.BinaryCentralOddOrder
public import Theory.GroupTheory.NormalPGroupTransitiveCentralizer
public import Theory.SpecificGroups.AlternatingFiveSylowNonsplitting
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ShortBenderModels

/-!
# Full short-centralizer containment when Mc equals the first endpoint

Transport the marked four-plane into the actual ambient short centralizer.
The local two-core centralizes this plane by conjugacy transitivity and the
local group is five-free. If the local centralizer were proper, I.8.5 and
the Bender alternatives would give a normal A₅ with exactly that Sylow
four-group. Its containment in the derived two-core contradicts the A₅
fixed-Sylow automorphism calculation.

This discharges F.4.42, printed p.295, for the Mc = H branch of original
14.2.18--19 and 14.3.15. The cubic partner branch remains separate. Every
transport uses the same literal endpoint marking; EightBorelAmbient supplies
the original ComponentLift/EightImageRow application.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

def shortLocalEquiv (r : MarkedTriality T M Mc H) (a : ExtensionField P) :
    centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H)) ≃*
      (secondParabolic T M Mc H).subgroupOf
        (centralizer ({(markedShortRoot r a : G)} : Set G)) where
  toFun x := ⟨⟨x.val.val, mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp x.val.property))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def shortPlaneInAmbient (r : MarkedTriality T M Mc H) (a : ExtensionField P) (ha : a ≠ 0) :
    Subgroup (centralizer ({(markedShortRoot r a : G)} : Set G)) :=
  (markedShortPlane r a ha).map
    (((secondParabolic T M Mc H).subgroupOf
      (centralizer ({(markedShortRoot r a : G)} : Set G))).subtype.comp
        (shortLocalEquiv r a).toMonoidHom)

omit [Finite G] in
theorem shortPlaneInAmbient_structure (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0) :
    let C := centralizer ({(markedShortRoot r a : G)} : Set G)
    let X := (secondParabolic T M Mc H).subgroupOf C
    let V := shortPlaneInAmbient r a ha
    V ≤ X ∧ (V.subgroupOf X).Normal ∧ IsElementaryAbelian 2 V ∧
      Nat.card V = 4 ∧ V ≤ ⁅X.pCoreIn 2,X.pCoreIn 2⁆ := by
  let C := centralizer ({(markedShortRoot r a : G)} : Set G)
  let X := (secondParabolic T M Mc H).subgroupOf C
  let D := centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))
  let W := markedShortPlane r a ha
  let eX := shortLocalEquiv r a
  let f := X.subtype.comp eX.toMonoidHom
  let V := shortPlaneInAmbient r a ha
  have hf : Function.Injective f := X.subtype_injective.comp eX.injective
  obtain ⟨hWn,hWe,hWc,hWd⟩ := marked_short_plane_structure r a ha
  let : W.Normal := hWn
  let : IsElementaryAbelian 2 W := hWe
  have hVX : V ≤ X := by
    rintro _ ⟨x,hx,rfl⟩
    exact (eX x).property
  have hVXeq : V.subgroupOf X = W.map eX.toMonoidHom := by
    change (W.map (X.subtype.comp eX.toMonoidHom)).comap X.subtype = _
    rw [←map_map,comap_map_eq_self_of_injective X.subtype_injective]
  refine ⟨hVX,?_,IsElementaryAbelian.map f,?_,?_⟩
  · rw [hVXeq]
    exact Subgroup.Normal.map hWn eX.toMonoidHom eX.surjective
  · exact (card_map_of_injective hf).trans hWc
  · have hd := map_mono (f := f) hWd
    rw [map_commutator] at hd
    have he : (pCore 2 D).map f = X.pCoreIn 2 := by
      rw [←map_map,pCore_map_iso]
      rfl
    rwa [he] at hd

/-- Local transitivity forces the two-core to centralize the actual plane. -/
theorem marked_short_core_centralizes_plane (r : MarkedTriality T M Mc H)
    (hTH : (T : Subgroup G) ≤ H) (a : ExtensionField P) (ha : a ≠ 0) :
    let D := centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))
    pCore 2 D ≤ centralizer (markedShortPlane r a ha : Set D) := by
  let D := centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))
  let V := markedShortPlane r a ha
  obtain ⟨hVn,_,hVc,_⟩ := marked_short_plane_structure r a ha
  let : V.Normal := hVn
  have hzcard : Nat.card (firstCoreCenter H) = 2 := by
    let := firstCore_extraspecial r
    rw [firstCoreCenter,card_map_of_injective (H.pCoreIn 2).subtype_injective]
    exact IsExtraspecial.center_order_p 2 (H.pCoreIn 2)
  obtain ⟨z,hzne,_⟩ := (Nat.card_eq_two_iff' (1 : firstCoreCenter H)).mp hzcard
  have hz1 : (z : G) ≠ 1 := fun hh => hzne (Subtype.ext hh)
  apply normal_pGroup_centralizes_of_transitive_nonidentity (pCore 2 D) V pCore_isPGroup
    (by rw [show Nat.card V = 4 from hVc]; decide)
  intro x hx hx1 y hy hy1
  obtain ⟨c,hc⟩ := marked_short_plane_orbit r hTH a ha z.property hz1 x hx
    (fun he => hx1 (Subtype.ext (Subtype.ext he)))
  obtain ⟨d,hd⟩ := marked_short_plane_orbit r hTH a ha z.property hz1 y hy
    (fun he => hy1 (Subtype.ext (Subtype.ext he)))
  refine ⟨d*c⁻¹,Subtype.ext (Subtype.ext ?_)⟩
  change ((d.val:G)*(c.val:G)⁻¹)*(x.val:G)*((d.val:G)*(c.val:G)⁻¹)⁻¹=(y.val:G)
  rw [←hc,←hd]
  group

/-- The local short centralizer has no factor five in its order. -/
theorem marked_short_five_free (r : MarkedTriality T M Mc H)
    (a : ExtensionField P) (ha : a ≠ 0) :
    ¬ 5 ∣ Nat.card (centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))) := by
  intro hd
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 5 hd
  let y := markedShortCentralizerEquiv r a ha x
  have hy : orderOf (y.val) = 5 := by
    rw [orderOf_coe]
    exact ((markedShortCentralizerEquiv r a ha).orderOf_eq x).trans hx
  have hh := _root_.Triality.Standard.BinaryCentralOddOrder.card_dvd_twentyOne
    (zpowers y.val) (by rw [Nat.card_zpowers,hy]; decide)
    (zpowers_le.mpr (_root_.Triality.Standard.ShortRootCentralizer.centralizer_le_central_two a ha y.property))
  rw [Nat.card_zpowers,hy] at hh
  norm_num at hh

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

theorem source_short_plane_unique_fixed (r : MarkedTriality T M Mc H)
    (hplain : Mc = H) (a : ExtensionField P) (ha : a ≠ 0) :
    let C := centralizer ({(markedShortRoot r a : G)} : Set G)
    let X := (secondParabolic T M Mc H).subgroupOf C
    ∀ x : C, x ∈ shortPlaneInAmbient r a ha → x ≠ 1 →
      ∃! q : C ⧸ X, x • q = q := by
  dsimp only
  obtain ⟨z,hzne,_⟩ := (Nat.card_eq_two_iff' (1 : centralInvolutions T)).mp
    (plane_centralInvolutions_card T M hM.1.2 hcard e)
  have hz1 : (z : G) ≠ 1 := fun hh => hzne (Subtype.ext hh)
  have hzQ : (z : G) ∈ firstCoreCenter H := by
    rw [source_firstCore_center hG hempty hM hu hmany hcard e hH r]
    exact z.property
  intro x hx hx1
  obtain ⟨y,hy,hye⟩ := hx
  have hy1 : (y.val : G) ≠ 1 := by
    intro hh
    apply hx1
    rw [←hye]
    exact Subtype.ext hh
  obtain ⟨c,hc⟩ := marked_short_plane_orbit r hH.1.1.2 a ha hzQ hz1 y hy hy1
  apply source_short_unique_fixed_of_partner_eq hG hempty hM hu hmany hcard e hH
    r hplain a ha z.property hz1 x
  apply isConj_iff.mpr
  refine ⟨(c.val : G),?_⟩
  exact hc.trans (congrArg Subtype.val hye)

theorem source_short_bender_of_proper (r : MarkedTriality T M Mc H)
    (hplain : Mc = H) (a : ExtensionField P) (ha : a ≠ 0)
    (hproper : ¬ centralizer ({(markedShortRoot r a : G)} : Set G) ≤ secondParabolic T M Mc H) :
    let C := centralizer ({(markedShortRoot r a : G)} : Set G)
    let X := (secondParabolic T M Mc H).subgroupOf C
    let V := shortPlaneInAmbient r a ha
    let L := normalClosure (V : Set C)
    let N := X.comap L.subtype
    IsQuasisimple L ∧ BenderSuzuki.IsSimpleBenderGroup (L ⧸ center L) ∧
      N = normalizer (V.subgroupOf L : Set L) ∧ BenderSuzuki.IsBorelSubgroup N ∧
      ∃ S : Sylow 2 L, (S : Subgroup L) ≤ N ∧
        V.subgroupOf L = (omega₁ S (p := 2)).map (S : Subgroup L).subtype := by
  let C := centralizer ({(markedShortRoot r a : G)} : Set G)
  let X := (secondParabolic T M Mc H).subgroupOf C
  let V := shortPlaneInAmbient r a ha
  obtain ⟨hVX,hVn,hVe,hVc,_⟩ := shortPlaneInAmbient_structure r a ha
  let : (V.subgroupOf X).Normal := hVn
  let : IsElementaryAbelian 2 V := hVe
  change Nat.card V = 4 at hVc
  have hVne : V ≠ ⊥ := by intro he; rw [he,card_bot] at hVc; omega
  have hXne : X ≠ ⊤ := by
    intro he
    apply hproper
    intro x hx
    exact show (⟨x,hx⟩ : C) ∈ X from he ▸ mem_top _
  exact (ChapterI.Section06To08.lemma_I_8_5_structure V X hVX hVne hXne
    (source_short_plane_unique_fixed hG hempty hM hu hmany hcard e hH r hplain a ha)).resolve_left
      (fun h => by have hh := h.1; omega)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic

namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH

theorem source_short_centralizer_le_of_partner_eq (r : MarkedTriality T M Mc H)
    (hplain : Mc = H) (a : ExtensionField P) (ha : a ≠ 0) :
    centralizer ({(markedShortRoot r a : G)} : Set G) ≤ secondParabolic T M Mc H := by
  by_contra hproper
  let C := centralizer ({(markedShortRoot r a : G)} : Set G)
  let X := (secondParabolic T M Mc H).subgroupOf C
  let D := centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))
  let V := shortPlaneInAmbient r a ha
  let eX := shortLocalEquiv r a
  let f := X.subtype.comp eX.toMonoidHom
  obtain ⟨hVX,hVn,hVe,hVc,hVd⟩ := shortPlaneInAmbient_structure r a ha
  let : (V.subgroupOf X).Normal := hVn
  let : IsElementaryAbelian 2 V := hVe
  have hXne : X ≠ ⊤ := by
    intro he
    apply hproper
    intro x hx
    exact show (⟨x,hx⟩ : C) ∈ X from he ▸ mem_top _
  have hXfive : ¬ 5 ∣ Nat.card X := by
    rw [←Nat.card_congr eX.toEquiv]
    exact marked_short_five_free r a ha
  obtain ⟨⟨eA⟩,S,hSV⟩ := CFSG.Quasithin.BinaryShortModels.unique_fixed_four_five_free_normalClosure
    V X hVX hVc hXfive hXne
    (source_short_plane_unique_fixed hG hempty hM hu hmany hcard e hH r hplain a ha)
  have heCore : (pCore 2 D).map f = X.pCoreIn 2 := by
    rw [←map_map,pCore_map_iso]
    rfl
  have hcentral : X.pCoreIn 2 ≤ centralizer (V : Set C) := by
    rw [←heCore]
    rintro q ⟨x,hx,rfl⟩ v ⟨w,hw,rfl⟩
    exact (map_mul f w x).symm.trans
      ((congrArg f ((marked_short_core_centralizes_plane r hH.1.1.2 a ha hx) w hw)).trans
        (map_mul f x w))
  have hbot := alternating_five_sylow_not_le_commutator_centralizer
    (normalClosure (V : Set C)) V (X.pCoreIn 2) eA S hSV hcentral hVd
  change Nat.card V = 4 at hVc
  rw [hbot,card_bot] at hVc
  omega

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
