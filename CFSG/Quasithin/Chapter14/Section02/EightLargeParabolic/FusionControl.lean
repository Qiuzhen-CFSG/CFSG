module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionSylow
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.CompletionStructure
public import Theory.SpecificGroups.Triality.ArmsFixedConjugator
public import Theory.GroupTheory.UniqueFixedCosetFusion

/-!
# Fusion control in the original triality endpoint join

The fixed core calculation now retains a conjugator in the second parabolic.
The original Mc-conjugation reduction and N_G(B)=Mc join M then realize all
returning central-class fusion in B=H join P₂, including the cubic case.
Sylow conjugacy extends this to the full endpoint join J=Mc join M. Since
C_G(z)=Mc, z fixes exactly one coset of J. The unique-fixed-coset theorem
therefore realizes all ambient Sylow fusion inside J.

The full ambient centralizer of a returning central involution in B also
lies in J. These conclusions retain the original endpoint maps. They do not
assert J=G, the second involution centralizer, or ambient recognition. The
marked realization remains the independent earlier input from 14.2.16.
The literal ComponentLift/EightImageRow application is EightBorelFusionControl.

Source: Aschbacher--Smith F.4.30--35 and the fusion argument preceding F.4.42,
printed pp.290--295; 14.2.18--19 and 14.3.15, printed pp.987,994.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.RadicalCoordinates.Centers
open _root_.Triality.Standard.RadicalCoordinates.LeviCommutators
open _root_.Triality.Standard.EvenInvolutionGeometry
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

/-- A nonidentity core element fixed modulo the center is conjugate to the
specified central involution by the original second endpoint. -/
theorem marked_fixed_core_conjugate (r : MarkedTriality T M Mc H)
    (hTH : (T:Subgroup G)≤H) (q : H.pCoreIn 2) (hq1 : (q:G)≠1)
    {z : G} (hz : z∈firstCoreCenter H) (hz1 : z≠1)
    (hfix : ∀ x∈(T:Subgroup G), ⁅x,(q:G)⁆∈firstCoreCenter H) :
    ∃ b : secondParabolic T M Mc H, (b:G)*(q:G)*(b:G)⁻¹=z := by
  have hTP : (T:Subgroup G)≤secondParabolic T M Mc H := le_sup_right.trans le_sup_left
  have hQT : H.pCoreIn 2≤(T:Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hTH)
    change H.pCoreIn 2≤((T:Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTH] at hh
  have hzQ : z∈H.pCoreIn 2 := (map_subtype_le _) hz
  let zH : H := ⟨z,pCoreIn_le 2 H hzQ⟩
  have hzm := marked_core_center_mem r zH hz
  have hzm1 : (r.left zH).val≠1 := by
    intro hh
    exact hz1 (congrArg Subtype.val (r.left.injective
      ((Subtype.ext hh).trans (map_one r.left).symm)))
  obtain ⟨v,hv⟩ := ArmsNormalization.fixed_mod_center_conjugate_highest_in_second P rfl
    (firstCoreEquiv r q) (by
      intro a
      have hu : short P rfl 0 a∈unipotent P :=
        descendSubgroup_mono P
          (RadicalCoordinates.rootSubgroup_le_positiveSubgroup P rfl .central)
          (short_mem P rfl .central 0 trivial a)
      obtain ⟨x,hx,hxe⟩ := marked_sylow_lift r hTH _ hu
      let y : H := ⟨q,pCoreIn_le 2 H q.property⟩
      have hh := marked_core_center_mem r ⁅x,y⁆ (hfix x hx)
      have hm := map_commutatorElement
        ((parabolic P .arms).subtype.comp r.left.toMonoidHom) x y
      change (r.left ⁅x,y⁆).val=⁅(r.left x).val,(r.left y).val⁆ at hm
      rw [hm,hxe,←firstCoreEquiv_val r q] at hh
      exact hh)
  have hv1 : v.val*(firstCoreEquiv r q).val*v.val⁻¹≠1 := by
    intro hh
    have hq := (MulAut.conj v.val).injective (hh.trans (map_one _).symm)
    exact hq1 (congrArg Subtype.val ((firstCoreEquiv r).injective
      ((Subtype.ext hq).trans (map_one _).symm)))
  have he : v.val*(firstCoreEquiv r q).val*v.val⁻¹=(r.left zH).val := by
    obtain ⟨a,_,ha⟩ := (Nat.card_eq_two_iff' (1:highestRoot P)).mp
      (show Nat.card (highestRoot P)=2 by exact card_highestRoot P rfl)
    exact congrArg Subtype.val ((ha ⟨_,hv⟩ (fun h => hv1 (congrArg Subtype.val h))).trans
      (ha ⟨_,hzm⟩ (fun h => hzm1 (congrArg Subtype.val h))).symm)
  let b := r.right.symm v
  refine ⟨b,?_⟩
  have he' : r.right (b*⟨q,hTP (hQT q.property)⟩*b⁻¹)=r.right ⟨z,hTP (hQT hzQ)⟩ := by
    apply Subtype.ext
    simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv,b,r.right.apply_symm_apply]
    rw [←marked_endpoint_value r ⟨pCoreIn_le 2 H q.property,hTP (hQT q.property)⟩,
      ←firstCoreEquiv_val r q,←marked_endpoint_value r ⟨zH.property,hTP (hQT hzQ)⟩]
    exact he
  exact congrArg Subtype.val (r.right.injective he')

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

/-- Fusion of the central involution into the original core is realized in
the base generated by the two original endpoints, even when Mc has a cubic supplement. -/
theorem source_core_fusion_control (r : MarkedTriality T M Mc H)
    (q : H.pCoreIn 2) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z (q:G)) :
    ∃ a : (H ⊔ secondParabolic T M Mc H : Subgroup G), (a:G)*(q:G)*(a:G)⁻¹=z := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hconj
  have he : MulAut.conj g z=(q:G) := hg
  obtain ⟨b,hb⟩ := source_core_fusion_fixed hG hempty hM hu hmany hcard e hH r g hz hz1
    (he.symm ▸ q.property)
  have hnQ := (source_partner_le_first_normalizer hG hempty hM hu hmany hcard e hH r).trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  let qb : H.pCoreIn 2 := ⟨MulAut.conj (b:G) (q:G),
    (mem_normalizer_iff.mp (hnQ b.property) _).mp q.property⟩
  have hq1 : (q:G)≠1 := by
    intro hh
    exact hz1 ((MulAut.conj g).injective ((he.trans hh).trans (map_one _).symm))
  have hqb1 : (qb:G)≠1 := fun hh => hq1 ((MulAut.conj (b:G)).injective
    (hh.trans (map_one _).symm))
  have hzC : z∈firstCoreCenter H :=
    (source_firstCore_center hG hempty hM hu hmany hcard e hH r).symm ▸ hz
  obtain ⟨w,hw⟩ := marked_fixed_core_conjugate r hH.1.1.2 qb hqb1 hzC hz1 (by
    intro x hx
    rw [source_firstCore_center hG hempty hM hu hmany hcard e hH r]
    simpa only [he] using hb x hx)
  have hbN : (b:G)∈normalizer ((H ⊔ secondParabolic T M Mc H:Subgroup G):Set G) := by
    rw [source_generated_normalizer_eq hG hempty hM hu hmany hcard e hH r]
    exact mem_sup_left b.property
  have ha : (b:G)⁻¹*(w:G)*(b:G)∈H ⊔ secondParabolic T M Mc H := by
    simpa only [inv_inv] using (mem_normalizer_iff.mp
      ((normalizer ((H ⊔ secondParabolic T M Mc H:Subgroup G):Set G)).inv_mem hbN) (w:G)).mp
      (mem_sup_right w.property)
  have hbc : (b:G)*z=z*(b:G) := mem_centralizer_singleton_iff.mp
    ((source_partner_eq_element_centralizer hG hempty hM hu hmany hcard e hH r hz hz1) ▸ b.property)
  refine ⟨⟨_,ha⟩,?_⟩
  change ((b:G)⁻¹*(w:G)*(b:G))*(q:G)*((b:G)⁻¹*(w:G)*(b:G))⁻¹=z
  calc
    _ = (b:G)⁻¹*((w:G)*(qb:G)*(w:G)⁻¹)*(b:G) := by
      change _=(b:G)⁻¹*((w:G)*((b:G)*(q:G)*(b:G)⁻¹)*(w:G)⁻¹)*(b:G)
      group
    _ = (b:G)⁻¹*z*(b:G) := by rw [hw]
    _ = z := by rw [mul_assoc,←hbc,inv_mul_cancel_left]

/-- The base generated by the original endpoints controls fusion of the
central involution back into the actual Sylow subgroup. -/
theorem source_sylow_fusion_control (r : MarkedTriality T M Mc H)
    {x z : G} (hx : x∈(T:Subgroup G)) (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z x) :
    ∃ a : (H ⊔ secondParabolic T M Mc H : Subgroup G), (a:G)*x*(a:G)⁻¹=z := by
  have hzsq : z^2=1 := by
    have hh := pow_card_eq_one' (x := (⟨z,hz⟩:centralInvolutions T))
    rw [plane_centralInvolutions_card T M hM.1.2 hcard e] at hh
    exact congrArg Subtype.val hh
  have hxsq : x^2=1 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hconj
    rw [←hg,conj_pow,hzsq,mul_one,mul_inv_cancel]
  obtain ⟨b,q,hq,_⟩ := marked_sylow_square_placement r hH.1.1.2 hx hxsq
  obtain ⟨a,ha⟩ := source_core_fusion_control hG hempty hM hu hmany hcard e hH r q hz hz1
    (hconj.trans (isConj_iff.mpr ⟨(b:G),hq.symm⟩))
  refine ⟨a*⟨b,mem_sup_right b.property⟩,?_⟩
  change ((a:G)*(b:G))*x*((a:G)*(b:G))⁻¹=z
  calc
    _ = (a:G)*((b:G)*x*(b:G)⁻¹)*(a:G)⁻¹ := by group
    _ = z := by rw [←hq,ha]

omit [Finite G] hG hempty hM hu hmany hcard e hH in
private theorem square_conjugate_into_sylow {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (x : A) (hx : x^2=1) :
    ∃ a : A, a*x*a⁻¹∈(S:Subgroup A) := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨R,hR⟩ := hp.exists_le_sylow
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq A R S
  refine ⟨a,?_⟩
  rw [←ha]
  exact ⟨x,hR (mem_zpowers x),rfl⟩

/-- Every returning ambient conjugate of the central involution in the whole
original generated base is conjugate there, including the cubic Mc case. -/
theorem source_generated_fusion_control (r : MarkedTriality T M Mc H)
    (x : (H ⊔ secondParabolic T M Mc H : Subgroup G)) {z : G}
    (hz : z∈centralInvolutions T) (hz1 : z≠1) (hconj : IsConj z (x:G)) :
    ∃ a : (H ⊔ secondParabolic T M Mc H : Subgroup G), (a:G)*(x:G)*(a:G)⁻¹=z := by
  have hTB : (T:Subgroup G)≤H ⊔ secondParabolic T M Mc H := fun _ hx => mem_sup_left (hH.1.1.2 hx)
  have hzsq : z^2=1 := by
    have hh := pow_card_eq_one' (x := (⟨z,hz⟩:centralInvolutions T))
    rw [plane_centralInvolutions_card T M hM.1.2 hcard e] at hh
    exact congrArg Subtype.val hh
  have hxsq : x^2=1 := by
    apply Subtype.ext
    obtain ⟨g,hg⟩ := isConj_iff.mp hconj
    change (x:G)^2=1
    rw [←hg,conj_pow,hzsq,mul_one,mul_inv_cancel]
  obtain ⟨b,hb⟩ := square_conjugate_into_sylow (T.subtype hTB) x hxsq
  have ht : (b:G)*(x:G)*(b:G)⁻¹∈(T:Subgroup G) := hb
  obtain ⟨a,ha⟩ := source_sylow_fusion_control hG hempty hM hu hmany hcard e hH r ht hz hz1
    (hconj.trans (isConj_iff.mpr ⟨(b:G),rfl⟩))
  refine ⟨a*b,?_⟩
  change ((a:G)*(b:G))*(x:G)*((a:G)*(b:G))⁻¹=z
  calc
    _ = (a:G)*((b:G)*(x:G)*(b:G)⁻¹)*(a:G)⁻¹ := by group
    _ = z := ha

/-- A conjugator returning the central involution to the generated base lies
in its full original normalizer Mc join M. -/
theorem source_returning_conjugator_mem (r : MarkedTriality T M Mc H)
    {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (g : G) (hg : MulAut.conj g z∈H ⊔ secondParabolic T M Mc H) :
    g∈Mc ⊔ M := by
  obtain ⟨a,ha⟩ := source_generated_fusion_control hG hempty hM hu hmany hcard e hH r
    ⟨MulAut.conj g z,hg⟩ hz hz1 (isConj_iff.mpr ⟨g,rfl⟩)
  have hBJ : (H ⊔ secondParabolic T M Mc H : Subgroup G)≤Mc ⊔ M := by
    rw [←source_generated_normalizer_eq hG hempty hM hu hmany hcard e hH r]
    exact le_normalizer
  have hag : (a:G)*g∈Mc := by
    apply (source_partner_eq_element_centralizer hG hempty hM hu hmany hcard e hH r hz hz1).ge
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      ((a:G)*g)*z*((a:G)*g)⁻¹=(a:G)*(MulAut.conj g z)*(a:G)⁻¹ := by
        change _=(a:G)*(g*z*g⁻¹)*(a:G)⁻¹
        group
      _ = z := ha
  simpa only [inv_mul_cancel_left] using
    (Mc ⊔ M).mul_mem ((Mc ⊔ M).inv_mem (hBJ a.property)) (mem_sup_left hag)

/-- The full ambient centralizer of every returning central involution in
the generated base lies in Mc join M. -/
theorem source_generated_long_centralizer_le (r : MarkedTriality T M Mc H)
    (x : (H ⊔ secondParabolic T M Mc H : Subgroup G)) {z : G}
    (hz : z∈centralInvolutions T) (hz1 : z≠1) (hconj : IsConj z (x:G)) :
    centralizer ({(x:G)}:Set G)≤Mc ⊔ M := by
  obtain ⟨a,ha⟩ := source_generated_fusion_control hG hempty hM hu hmany hcard e hH r x hz hz1 hconj
  have hBJ : (H ⊔ secondParabolic T M Mc H : Subgroup G)≤Mc ⊔ M := by
    rw [←source_generated_normalizer_eq hG hempty hM hu hmany hcard e hH r]
    exact le_normalizer
  intro g hg
  have hc : (a:G)*g*(a:G)⁻¹∈Mc := by
    apply (source_partner_eq_element_centralizer hG hempty hM hu hmany hcard e hH r hz hz1).ge
    apply mem_centralizer_singleton_iff.mpr
    rw [←ha]
    have hh := mem_centralizer_singleton_iff.mp hg
    calc
      ((a:G)*g*(a:G)⁻¹)*((a:G)*(x:G)*(a:G)⁻¹) = (a:G)*(g*(x:G))*(a:G)⁻¹ := by group
      _ = (a:G)*((x:G)*g)*(a:G)⁻¹ := by rw [hh]
      _ = ((a:G)*(x:G)*(a:G)⁻¹)*((a:G)*g*(a:G)⁻¹) := by group
  have hm := (Mc ⊔ M).mul_mem ((Mc ⊔ M).mul_mem
    ((Mc ⊔ M).inv_mem (hBJ a.property)) (mem_sup_left hc)) (hBJ a.property)
  simpa only [inv_mul_cancel_left,mul_assoc,inv_mul_cancel_right,inv_mul_cancel,mul_one] using hm

/-- The full original endpoint join controls the returning central class. -/
theorem source_extended_fusion_control (r : MarkedTriality T M Mc H)
    (x : (Mc ⊔ M : Subgroup G)) {z : G}
    (hz : z∈centralInvolutions T) (hz1 : z≠1) (hconj : IsConj z (x:G)) :
    ∃ a : (Mc ⊔ M : Subgroup G), (a:G)*(x:G)*(a:G)⁻¹=z := by
  have hTJ : (T:Subgroup G)≤Mc ⊔ M := fun _ hx => mem_sup_right (hM.1.2 hx)
  have hBJ : (H ⊔ secondParabolic T M Mc H : Subgroup G)≤Mc ⊔ M := by
    rw [←source_generated_normalizer_eq hG hempty hM hu hmany hcard e hH r]
    exact le_normalizer
  have hzsq : z^2=1 := by
    have hh := pow_card_eq_one' (x := (⟨z,hz⟩:centralInvolutions T))
    rw [plane_centralInvolutions_card T M hM.1.2 hcard e] at hh
    exact congrArg Subtype.val hh
  have hxsq : x^2=1 := by
    apply Subtype.ext
    obtain ⟨g,hg⟩ := isConj_iff.mp hconj
    change (x:G)^2=1
    rw [←hg,conj_pow,hzsq,mul_one,mul_inv_cancel]
  obtain ⟨b,hb⟩ := square_conjugate_into_sylow (T.subtype hTJ) x hxsq
  have ht : (b:G)*(x:G)*(b:G)⁻¹∈(T:Subgroup G) := hb
  obtain ⟨a,ha⟩ := source_sylow_fusion_control hG hempty hM hu hmany hcard e hH r ht hz hz1
    (hconj.trans (isConj_iff.mpr ⟨(b:G),rfl⟩))
  refine ⟨⟨a,hBJ a.property⟩*b,?_⟩
  change ((a:G)*(b:G))*(x:G)*((a:G)*(b:G))⁻¹=z
  calc
    _ = (a:G)*((b:G)*(x:G)*(b:G)⁻¹)*(a:G)⁻¹ := by group
    _ = z := ha

/-- The original central involution fixes a unique coset of Mc join M. -/
theorem source_central_unique_fixed (r : MarkedTriality T M Mc H)
    {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1) :
    ∃! q : G ⧸ (Mc ⊔ M), z • q=q := by
  apply UniqueFixedCoset.unique_of_fusion_and_centralizer
    (mem_sup_right (hM.1.2 (centralInvolutions_le_sylow T hz)))
  · rw [←source_partner_eq_element_centralizer hG hempty hM hu hmany hcard e hH r hz hz1]
    exact le_sup_left
  · intro g hg
    obtain ⟨a,ha⟩ := source_extended_fusion_control hG hempty hM hu hmany hcard e hH r
      ⟨g*z*g⁻¹,hg⟩ hz hz1 (isConj_iff.mpr ⟨g,rfl⟩)
    refine ⟨(a:G)⁻¹,(Mc ⊔ M).inv_mem a.property,?_⟩
    have hh := congrArg (fun u:G => (a:G)⁻¹*u*(a:G)) ha
    simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,mul_inv_cancel_left,inv_mul_cancel,mul_one] using hh

/-- All fusion on the actual ambient Sylow is controlled by Mc join M. -/
theorem source_sylow_full_fusion_control (r : MarkedTriality T M Mc H)
    {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    {x y : G} (hx : x∈(T:Subgroup G)) (hy : y∈(T:Subgroup G))
    (hxy : IsConj x y) : ∃ a∈Mc ⊔ M, a*x*a⁻¹=y := by
  apply UniqueFixedCoset.sylow_fusion T (fun _ hx => mem_sup_right (hM.1.2 hx))
    (centralInvolutions_le_sylow T hz) ?_
    (source_central_unique_fixed hG hempty hM hu hmany hcard e hH r hz hz1) hx hy hxy
  intro t ht
  exact (show t*z=z*t from centralInvolutions_le_centralizer_sylow T hz t ht).symm

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
