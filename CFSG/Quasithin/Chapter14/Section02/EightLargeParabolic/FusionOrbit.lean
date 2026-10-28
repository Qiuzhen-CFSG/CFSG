module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionSeparation
public import Theory.GroupTheory.ExtraspecialCentralizingPair
public import Theory.SpecificGroups.Triality.ArmsOrbitTransport

/-!
# Full returning-core fusion in the original triality marking

Every element of the extraspecial core centralizes a pair whose commutator is
the nonidentity central involution. This removes the representative restriction
from the mutual-core reduction: any ambient conjugate of z returning to Q has
an Mc-conjugate fixed modulo Z. A Frattini factorization of Mc through the
original Sylow normalizer then proves that its image under the original first
endpoint marking is a long-root involution, even in the cubic extension.

The compatible intrinsic action also bounds its Q/Z orbit by nine, excluding
the entire highest-short-root quotient orbit and its central lifts. These
results apply in EightBorelFusionOrbit to ComponentLift and EightImageRow.
The marked realization remains the independent earlier input; full Sylow
fusion, the second involution centralizer, ambient recognition and the Borel
contradiction are not asserted here.

Source: Aschbacher--Smith F.4.35, printed p.292, in the original
14.2.18--19 setup, printed p.987.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.EvenInvolutionGeometry
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

/-- Arbitrary returning central involutions admit the original mutual-core fixed-space reduction. -/
theorem source_core_fusion_fixed (r : MarkedTriality T M Mc H)
    (a : G) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (htQ : MulAut.conj a z∈H.pCoreIn 2) :
    ∃ b : Mc, ∀ x∈(T:Subgroup G),
      ⁅x,MulAut.conj (b:G) (MulAut.conj a z)⁆∈centralInvolutions T := by
  by_cases ha : a∈Mc
  · have hMc := source_partner_eq_element_centralizer hG hempty hM hu hmany hcard e hH r hz hz1
    have he : MulAut.conj a z=z := by
      change a*z*a⁻¹=z
      have hc := mem_centralizer_singleton_iff.mp (hMc ▸ ha)
      calc
        a*z*a⁻¹=(z*a)*a⁻¹ := congrArg (fun u:G => u*a⁻¹) hc
        _ = z := by group
    refine ⟨1,?_⟩
    intro x hx
    change ⁅x,1*(MulAut.conj a z)*1⁻¹⁆∈centralInvolutions T
    rw [he,one_mul,inv_one,mul_one]
    have hc : x*z=z*x := centralInvolutions_le_centralizer_sylow T hz x hx
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
    exact one_mem _
  · have hzC : z∈firstCoreCenter H :=
      (source_firstCore_center hG hempty hM hu hmany hcard e hH r).symm ▸ hz
    obtain ⟨zQ,hzQ,hzval⟩ := hzC
    let := firstCore_extraspecial r
    obtain ⟨x,y,hx,hy,hxy⟩ := ExtraspecialIntersection.centralizing_pair_of_card_gt_eight
      (show 8<Nat.card (H.pCoreIn 2) by rw [firstCore_card r]; decide)
      (⟨MulAut.conj a z,htQ⟩ : H.pCoreIn 2) zQ hzQ
      (fun he => hz1 ((hzval.symm.trans (congrArg Subtype.val he))))
    obtain ⟨a',ha',ht',hz'⟩ := source_pair_mutual_core hG hempty hM hu hmany hcard e hH r
      a ha hz hz1 x.property y.property
      (hx.map (H.pCoreIn 2).subtype) (hy.map (H.pCoreIn 2).subtype)
      ((congrArg Subtype.val hxy).trans hzval)
    obtain ⟨b,hb⟩ := source_mutual_core_fusion_reduction hG hempty hM hu hmany hcard e hH r
      a' ha' hz hz1 hz' (ht'.symm ▸ htQ)
    exact ⟨b,by simpa only [ht'] using hb⟩

private theorem partner_sylow_factorization (r : MarkedTriality T M Mc H) :
    Mc = H ⊔ (normalizer (T:Set G) ⊓ Mc) := by
  have hHM := source_first_le_partner hG hempty hM hu hmany hcard e hH
  have hTM := hH.1.1.2.trans hHM
  let S := T.subtype hTM
  let B := H.subgroupOf Mc
  let : B.Normal := (source_first_normal_component hG hempty hM hu hmany hcard e hH r).2
  have ht := S.normalizer_sup_eq_top' (show (S:Subgroup Mc)≤B from comap_mono hH.1.1.2)
  apply le_antisymm ?_ (sup_le hHM inf_le_right)
  have hh : (⊤:Subgroup Mc)≤(H ⊔ (normalizer (T:Set G) ⊓ Mc)).subgroupOf Mc := by
    rw [←ht]
    refine sup_le ?_ (comap_mono le_sup_left)
    intro x hx
    have hx' : (x:G)∈normalizer (T:Set G) := by
      change x∈normalizer ((T:Subgroup G).subgroupOf Mc:Set Mc) at hx
      rw [←subgroupOf_normalizer_eq hTM] at hx
      exact hx
    exact mem_sup_right ⟨hx',x.property⟩
  intro x hx
  exact hh (show (⟨x,hx⟩:Mc)∈(⊤:Subgroup Mc) from mem_top _)

private theorem fixed_core_conjugate_by_sylow_normalizer (r : MarkedTriality T M Mc H)
    (q : H.pCoreIn 2) (hfix : ∀ x∈(T:Subgroup G), ⁅x,(q:G)⁆∈centralInvolutions T)
    (n : G) (hn : n∈normalizer (T:Set G) ⊓ Mc) :
    ∀ x∈(T:Subgroup G), ⁅x,MulAut.conj n (q:G)⁆∈centralInvolutions T := by
  intro x hx
  have hnx : MulAut.conj n⁻¹ x∈(T:Subgroup G) :=
    (mem_normalizer_iff.mp ((normalizer (T:Set G)).inv_mem hn.1) x).mp hx
  have hc := hfix _ hnx
  have hnC : n∈centralizer (centralInvolutions T:Set G) := by
    rw [←source_firstCore_center hG hempty hM hu hmany hcard e hH r,
      ←source_partner_centralizer hG hempty hM hu hmany hcard e hH r]
    exact hn.2
  have hconj : MulAut.conj n ⁅MulAut.conj n⁻¹ x,(q:G)⁆=⁅MulAut.conj n⁻¹ x,(q:G)⁆ := by
    change n*_ *n⁻¹=_
    rw [←hnC _ hc,mul_inv_cancel_right]
  have hnx' : MulAut.conj n (MulAut.conj n⁻¹ x)=x := by
    change n*(n⁻¹*x*(n⁻¹)⁻¹)*n⁻¹=x
    group
  rw [map_commutatorElement,hnx'] at hconj
  exact hconj.symm ▸ hc

/-- Every ambient conjugate of the central involution returning to the original
core has a long-root image under the same endpoint marking, including cubic Mc. -/
theorem source_core_fusion_isLongRoot (r : MarkedTriality T M Mc H)
    (q : H.pCoreIn 2) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z (q:G)) :
    IsLongRootInvolution 1 Nat.zero_lt_one (firstCoreEquiv r q).val := by
  obtain ⟨a,ha⟩ := isConj_iff.mp hconj
  have he : MulAut.conj a z=(q:G) := ha
  have hq1 : (q:G)≠1 := fun h => hz1 ((MulAut.conj a).injective
    ((he.trans h).trans (map_one _).symm))
  obtain ⟨b,hb⟩ := source_core_fusion_fixed hG hempty hM hu hmany hcard e hH r a hz hz1
    (he.symm ▸ q.property)
  have hnQ : Mc≤normalizer (H.pCoreIn 2:Set G) :=
    (source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r).trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  let qb : H.pCoreIn 2 := ⟨MulAut.conj (b:G) (q:G),
    (mem_normalizer_iff.mp (hnQ b.property) _).mp q.property⟩
  have hqb : ∀ x∈(T:Subgroup G), ⁅x,(qb:G)⁆∈centralInvolutions T := by
    simpa only [he] using hb
  have hprod : (b:G)⁻¹∈(H:Set G)*((normalizer (T:Set G) ⊓ Mc:Subgroup G):Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left H (normalizer (T:Set G) ⊓ Mc)
      (inf_le_right.trans (source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r)),
      ←partner_sylow_factorization hG hempty hM hu hmany hcard e hH r]
    exact Mc.inv_mem b.property
  obtain ⟨h,hh,n,hn,hhn⟩ := hprod
  change h*n=(b:G)⁻¹ at hhn
  let qn : H.pCoreIn 2 := ⟨MulAut.conj n (qb:G),
    (mem_normalizer_iff.mp (hnQ hn.2) _).mp qb.property⟩
  have hqn : ∀ x∈(T:Subgroup G), ⁅x,(qn:G)⁆∈firstCoreCenter H := by
    rw [source_firstCore_center hG hempty hM hu hmany hcard e hH r]
    exact fixed_core_conjugate_by_sylow_normalizer hG hempty hM hu hmany hcard e hH r qb hqb n hn
  have hqn1 : (qn:G)≠1 := by
    intro hh
    have hqbone := (MulAut.conj n).injective (hh.trans (map_one _).symm)
    exact hq1 ((MulAut.conj (b:G)).injective (hqbone.trans (map_one _).symm))
  have hlong := marked_fixed_core_isLongRoot r hH.1.1.2 qn hqn1 hqn
  apply hlong.of_isConj 1 Nat.zero_lt_one
  refine isConj_iff.mpr ⟨(r.left ⟨h,hh⟩).val,?_⟩
  rw [firstCoreEquiv_val r qn,firstCoreEquiv_val r q]
  have hv : h*(qn:G)*h⁻¹=(q:G) := by
    change h*(n*((b:G)*(q:G)*(b:G)⁻¹)*n⁻¹)*h⁻¹=(q:G)
    calc
      _ = (h*n)*((b:G)*(q:G)*(b:G)⁻¹)*(h*n)⁻¹ := by group
      _ = _ := by rw [hhn]; group
  have hsub : (⟨h,hh⟩:H)*⟨qn,pCoreIn_le 2 H qn.property⟩*(⟨h,hh⟩:H)⁻¹=
      ⟨q,pCoreIn_le 2 H q.property⟩ := Subtype.ext hv
  simpa only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv] using
    congrArg (fun x : H => (r.left x).val) hsub

/-- Every returning central involution has intrinsic Q/Z orbit of size at most nine. -/
theorem source_core_fusion_orbit_bound (r : MarkedTriality T M Mc H)
    (q : H.pCoreIn 2) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z (q:G)) :
    (ArmsOrbit.points (ArmsOrbit.point (firstCoreEquiv r q))).ncard≤9 := by
  obtain ⟨a,ha⟩ := isConj_iff.mp hconj
  have he : MulAut.conj a z=(q:G) := ha
  obtain ⟨b,hb⟩ := source_core_fusion_fixed hG hempty hM hu hmany hcard e hH r a hz hz1
    (he.symm ▸ q.property)
  have hfix : ∀ x∈(T:Subgroup G), ⁅x,MulAut.conj (b:G) (q:G)⁆∈centralInvolutions T := by
    simpa only [he] using hb
  let f := firstCoreEquiv r
  have hbN := source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r b.property
  have hn := normalizer_le_normalizer_characteristic_image H (pCore 2 H) hbN
  let α := MulAut.congr r.left (H.normalizerMonoidHom ⟨b,hbN⟩)
  let c := MulAut.congr f ((H.pCoreIn 2).normalizerMonoidHom ⟨b,hn⟩)
  let cq := (H.pCoreIn 2).normalizerMonoidHom ⟨b,hn⟩ q
  have hcq : c (f q)=f cq := by
    change f ((H.pCoreIn 2).normalizerMonoidHom ⟨b,hn⟩ (f.symm (f q)))=f cq
    rw [f.symm_apply_apply]
  have hbound : (ArmsOrbit.points (ArmsOrbit.point (c (f q)))).ncard≤9 := by
    apply ArmsOrbit.fixed_point_orbit_bound
    intro h hh
    rw [hcq]
    obtain ⟨x,hx,hxe⟩ := marked_sylow_lift r hH.1.1.2 h.val hh
    have hxr : r.left x=h := Subtype.ext hxe
    let y : H := ⟨cq,pCoreIn_le 2 H cq.property⟩
    have hzC := hfix x hx
    rw [←source_firstCore_center hG hempty hM hu hmany hcard e hH r] at hzC
    have hm := marked_core_center_mem r ⁅x,y⁆ hzC
    have hm' : (r.left ⁅x,y⁆).val=⁅(r.left x).val,(r.left y).val⁆ :=
      map_commutatorElement ((parabolic (binaryParameters 1 Nat.zero_lt_one) .arms).subtype.comp
        r.left.toMonoidHom) x y
    rw [hm',←firstCoreEquiv_val r cq,hxr] at hm
    exact (ArmsOrbit.action_point_fixed_iff h (f cq)).mpr hm
  rw [ArmsOrbit.point_orbit_card_eq_of_core_compatible α c
    (marked_core_automorphism_compatible r b hbN) (f q)] at hbound
  exact hbound

/-- The entire short-root quotient orbit is disjoint from returning ambient central involutions. -/
theorem source_core_short_orbit_not_fused (r : MarkedTriality T M Mc H)
    (q : H.pCoreIn 2) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z (q:G))
    (d : ExtensionField (binaryParameters 1 Nat.zero_lt_one)) (hd : d≠0)
    (hshort : ArmsOrbit.point (firstCoreEquiv r q)∈
      ArmsOrbit.points (ArmsOrbit.point ⟨_,ArmsOrbit.short_two_mem d⟩)) : False := by
  have hupp := source_core_fusion_orbit_bound hG hempty hM hu hmany hcard e hH r q hz hz1 hconj
  have hlow := ArmsOrbit.short_orbit_point_lower d hd _ hshort
  omega
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
