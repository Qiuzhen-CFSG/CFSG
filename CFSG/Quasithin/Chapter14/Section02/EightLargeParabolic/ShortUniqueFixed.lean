module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.InvolutionFusion
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.ShortAmbient.Counting
public import Theory.SpecificGroups.Triality.SylowFixerThreeRank

/-!
# Fixed cosets and the short-plane normalizer when Mc equals H

When the original full long centralizer Mc is the marked first endpoint H,
its endpoint map identifies it with the native full long centralizer.
The other endpoint identifies the local short centralizer with the native
full short centralizer. Ambient endpoint fusion and short-root extremality
then permit the commuting-class double count: every long involution in
C_G(t) fixes a unique coset of its original local short centralizer.

The original central involution lies in the normal four-plane. Uniqueness
therefore traps every element of C_G(t) normalizing that plane in the local
centralizer, giving its exact normalizer there.

This proves the fixed-coset and normalizer steps in Aschbacher--Smith
F.4.42, printed p.295, for the Mc = H branch of 14.2.18--19 and 14.3.15.
The cubic branch and the nonsplitting argument giving full ambient short
centralizer containment remain with this source family. The literal
ComponentLift/EightImageRow consumer is EightBorelExtremality.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
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

/-- The literal local short centralizer has unique fixed cosets for every
ambient long involution, in the branch where Mc is the first endpoint. -/
theorem source_short_unique_fixed_of_partner_eq (r : MarkedTriality T M Mc H)
    (hplain : Mc = H) (a : ExtensionField P) (ha : a ≠ 0)
    {z : G} (hz : z ∈ centralInvolutions T) (hz1 : z ≠ 1) :
    let C := centralizer ({(markedShortRoot r a : G)} : Set G)
    ∀ x : C, IsConj z (x : G) →
      ∃! q : C ⧸ (secondParabolic T M Mc H).subgroupOf C, x • q = q := by
  let L := secondParabolic T M Mc H
  let f : L →* Carrier P := (parabolic P .central).subtype.comp r.right.toMonoidHom
  let g : H →* Carrier P := (parabolic P .arms).subtype.comp r.left.toMonoidHom
  have hf : Function.Injective f := (parabolic P .central).subtype_injective.comp r.right.injective
  have hg : Function.Injective g := (parabolic P .arms).subtype_injective.comp r.left.injective
  have hzH : z ∈ H := hH.1.1.2 (centralInvolutions_le_sylow T hz)
  let zH : H := ⟨z,hzH⟩
  have hz2 : orderOf z = 2 := by
    have hc := plane_centralInvolutions_card T M hM.1.2 hcard e
    have hn : (⟨z,hz⟩ : centralInvolutions T) ≠ 1 := fun hh => hz1 (congrArg Subtype.val hh)
    exact (Subgroup.orderOf_coe ⟨z,hz⟩).trans
      (orderOf_eq_prime (by
        have hh := pow_card_eq_one' (x := (⟨z,hz⟩ : centralInvolutions T))
        rwa [hc] at hh) hn)
  have hCz : centralizer ({z} : Set G) = H :=
    (source_partner_eq_element_centralizer hG hempty hM hu hmany hcard e hH r hz hz1).symm.trans hplain
  have hmodelZ : centralizer ({g zH} : Set (Carrier P)) = parabolic P .arms := by
    rw [highestRoot_centralizer_eq_localFactor 1 Nat.zero_lt_one (g zH)
      (marked_core_center_mem r zH (by rwa [source_firstCore_center hG hempty hM hu hmany hcard e hH r]))
      (fun hh => hz1 (congrArg Subtype.val (hg (hh.trans g.map_one.symm)))),
      parabolic_arms_eq_localFactor_at_two P rfl (by simp only [binaryParameters_q,pow_one])]
  apply ChapterF.SourceCompletion.GeneralReeFour.ShortAmbient.unique_fixed_of_endpoint_fusion
    L H f g hf hg (markedShortRoot r a) zH (markedShortRoot_order r a ha) hz2
    hCz.le ?_ ?_ ?_ ?_
  · rw [hCz,subgroupOf_self,hmodelZ]
    ext y
    constructor
    · rintro ⟨x,_,rfl⟩
      exact (r.left x).property
    · intro hy
      refine ⟨r.left.symm ⟨y,hy⟩,mem_top _,?_⟩
      exact congrArg Subtype.val (r.left.apply_symm_apply _)
  · change ((centralizer ({(markedShortRoot r a : G)} : Set G)).subgroupOf L).map f = _
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change (r.right x).val ∈ centralizer ({(r.right (markedShortRoot r a)).val} : Set (Carrier P))
      rw [markedShortRoot_image]
      exact (markedShortCentralizerEquiv r a ha ⟨x,
        mem_centralizer_singleton_iff.mpr (Subtype.ext
          (mem_centralizer_singleton_iff.mp hx))⟩).property
    · intro y hy
      have hy' : y ∈ centralizer ({RadicalCoordinates.LeviCommutators.short P rfl 2 a} : Set (Carrier P)) := by
        simpa only [show f (markedShortRoot r a) = RadicalCoordinates.LeviCommutators.short P rfl 2 a from
          markedShortRoot_image r a] using hy
      obtain ⟨x,hx⟩ := (markedShortCentralizerEquiv r a ha).surjective ⟨y,hy'⟩
      exact ⟨x.val,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property)),
        congrArg Subtype.val hx⟩
  · intro x y hx hy
    have hh := source_first_second_fusion_iff hG hempty hM hu hmany hcard e hH r y x hy hx
    exact ⟨fun h => (hh.mp h.symm).symm, fun h => (hh.mpr h.symm).symm⟩
  · obtain ⟨S,hS⟩ := source_short_ambient_sylow hG hempty hM hu hmany hcard e hH r a ha
    refine ⟨S,?_⟩
    rw [hS]
    exact fun x hx => (show (T : Subgroup G) ≤ L from le_sup_right.trans le_sup_left) hx


/-- The four-plane has exactly the original local short centralizer as its
normalizer inside the full ambient short centralizer, when Mc = H. -/
theorem source_short_plane_normalizer_of_partner_eq (r : MarkedTriality T M Mc H)
    (hplain : Mc = H) (a : ExtensionField P) (ha : a ≠ 0) :
    let D := centralizer ({markedShortRoot r a} : Set (secondParabolic T M Mc H))
    let C := centralizer ({(markedShortRoot r a : G)} : Set G)
    let f := (secondParabolic T M Mc H).subtype.comp D.subtype
    normalizer ((markedShortPlane r a ha).map f : Set G) ⊓ C =
      secondParabolic T M Mc H ⊓ C := by
  let L := secondParabolic T M Mc H
  let D := centralizer ({markedShortRoot r a} : Set L)
  let C := centralizer ({(markedShortRoot r a : G)} : Set G)
  let f : D →* G := L.subtype.comp D.subtype
  let V := markedShortPlane r a ha
  let W := V.map f
  change normalizer (W : Set G) ⊓ C = L ⊓ C
  have hWL : W ≤ L := by
    rintro _ ⟨x,_,rfl⟩
    exact x.val.property
  obtain ⟨z,hzne,_⟩ := (Nat.card_eq_two_iff' (1 : centralInvolutions T)).mp
    (plane_centralInvolutions_card T M hM.1.2 hcard e)
  have hz1 : (z : G) ≠ 1 := fun hh => hzne (Subtype.ext hh)
  have hzQ : (z : G) ∈ firstCoreCenter H := by
    rw [source_firstCore_center hG hempty hM hu hmany hcard e hH r]
    exact z.property
  obtain ⟨zD,hzD,hzV⟩ := marked_short_plane_contains_center r hH.1.1.2 a ha hzQ hz1
  have hzC : (z : G) ∈ C := by
    rw [←hzD]
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp zD.property))
  let zC : C := ⟨z,hzC⟩
  have hzW : (z : G) ∈ W := ⟨zD,hzV,hzD⟩
  apply le_antisymm
  · intro u huMem
    have hfz := source_short_unique_fixed_of_partner_eq hG hempty hM hu hmany hcard e hH r hplain a ha
      z.property hz1 zC (IsConj.refl _)
    have huW : u*(z:G)*u⁻¹ ∈ W := (mem_normalizer_iff.mp huMem.1 z).mp hzW
    have huX : (⟨u,huMem.2⟩ : C) ∈ L.subgroupOf C :=
      UniqueFixedCoset.transporter_mem (hWL hzW) hfz (hWL huW)
    exact ⟨huX,huMem.2⟩
  · intro u huMem
    have huD : (⟨u,huMem.1⟩ : L) ∈ D :=
      mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp huMem.2))
    let : V.Normal := (marked_short_plane_structure r a ha).1
    have huN : (⟨⟨u,huMem.1⟩,huD⟩ : D) ∈ normalizer (V : Set D) := by
      rw [normalizer_eq_top]
      exact mem_top _
    exact ⟨V.le_normalizer_map f ⟨_,huN,rfl⟩,huMem.2⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
