module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionOrbit
public import Theory.SpecificGroups.Triality.SylowInvolutionPlacement

/-!
# Returning involutions on the original Sylow and both parabolics

The second marked endpoint moves each square-one Sylow element into the
original extraspecial core. Both commuting squares retain the model equation
for this same conjugator. The returning-core theorem then shows that every
ambient conjugate of the central involution returning to the chosen Sylow has
a long-root image under the first endpoint marking. Conjugacy into the Sylow
inside each endpoint extends that conclusion to both whole parabolics.

The normalized core element also retains the intrinsic Q/Z orbit bound of
nine. The literal ComponentLift/EightImageRow application is in
EightBorelFusionSylow. This proves the returning-central-class direction;
the full fusion comparison, second involution centralizer, matching relation,
ambient generation and final Borel contradiction remain separate obligations.
The earlier marked realization remains explicit, including in the cubic case.

Source: Aschbacher--Smith F.4.30--35, printed pp.289--292, applied in
14.2.18--19 and 14.3.15, printed pp.987,994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.EvenInvolutionGeometry
local notation "P" => binaryParameters 1 Nat.zero_lt_one
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}

private theorem inclusion_left_value {L R : Type*} [Group L] [Group R]
    (A B C : Subgroup L) (hA : B≤A) (hC : B≤C)
    (A' B' C' : Subgroup R) (hA' : B'≤A') (hC' : B'≤C')
    (r : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups A B C hA hC)
      (RankTwoAmalgam.ofSubgroups A' B' C' hA' hC')) (x : B) :
    (r.left ⟨x,hA x.property⟩).val=(r.middle x).val :=
  congrArg Subtype.val (r.left_commutes x)

private theorem inclusion_endpoint_value {L R : Type*} [Group L] [Group R]
    (A B C : Subgroup L) (hA : B≤A) (hC : B≤C)
    (A' B' C' : Subgroup R) (hA' : B'≤A') (hC' : B'≤C')
    (r : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups A B C hA hC)
      (RankTwoAmalgam.ofSubgroups A' B' C' hA' hC')) (x : B) :
    (r.left ⟨x,hA x.property⟩).val=(r.right ⟨x,hC x.property⟩).val :=
  (congrArg Subtype.val (r.left_commutes x)).trans
    (congrArg Subtype.val (r.right_commutes x)).symm

omit [Finite G] in
/-- The two marked endpoint values agree on their actual intersection. -/
theorem marked_endpoint_value (r : MarkedTriality T M Mc H)
    {x : G} (hx : x∈H ⊓ secondParabolic T M Mc H) :
    (r.left ⟨x,hx.1⟩).val=(r.right ⟨x,hx.2⟩).val := by
  exact inclusion_endpoint_value H (H ⊓ secondParabolic T M Mc H)
    (secondParabolic T M Mc H) inf_le_left inf_le_right _ _ _
    (borel_le_parabolic P .arms) (borel_le_parabolic P .central) r ⟨x,hx⟩

/-- The first endpoint sends the chosen Sylow to the literal model unipotent subgroup. -/
theorem marked_sylow_image (r : MarkedTriality T M Mc H)
    (hTH : (T:Subgroup G)≤H) {x : G} (hx : x∈(T:Subgroup G)) :
    (r.left ⟨x,hTH hx⟩).val∈unipotent P := by
  have hTP : (T:Subgroup G)≤secondParabolic T M Mc H :=
    le_sup_right.trans le_sup_left
  let b : (H ⊓ secondParabolic T M Mc H : Subgroup G) := ⟨x,hTH hx,hTP hx⟩
  have hm : (r.middle b).val∈unipotent P := by
    rw [←middle_sylow_map r hTH]
    exact mem_map_of_mem _ (mem_map_of_mem _ hx)
  have he := inclusion_left_value H (H ⊓ secondParabolic T M Mc H)
    (secondParabolic T M Mc H) inf_le_left inf_le_right _ _ _
    (borel_le_parabolic P .arms) (borel_le_parabolic P .central) r b
  exact he.symm ▸ hm

/-- Every square-one element of the original Sylow is moved into its original
first core by the second endpoint; the model conjugation equation is retained. -/
theorem marked_sylow_square_placement (r : MarkedTriality T M Mc H)
    (hTH : (T:Subgroup G)≤H) {x : G} (hx : x∈(T:Subgroup G)) (hs : x^2=1) :
    ∃ b : secondParabolic T M Mc H, ∃ q : H.pCoreIn 2,
      (q:G)=(b:G)*x*(b:G)⁻¹ ∧
      (firstCoreEquiv r q).val=(r.right b).val*(r.left ⟨x,hTH hx⟩).val*(r.right b).val⁻¹ := by
  have hTP : (T:Subgroup G)≤secondParabolic T M Mc H :=
    le_sup_right.trans le_sup_left
  let xH : H := ⟨x,hTH hx⟩
  let u : unipotent P := ⟨(r.left xH).val,marked_sylow_image r hTH hx⟩
  have hus : u^2=1 := by
    apply Subtype.ext
    have hxH : xH^2=1 := Subtype.ext hs
    exact congrArg (fun t : parabolic P .arms => t.val) ((map_pow r.left xH 2).symm.trans
      ((congrArg r.left hxH).trans (map_one _)))
  obtain ⟨g,hg⟩ := unipotent_square_conjugate_mem_arms 1 Nat.zero_lt_one u hus
  let q := (firstCoreEquiv r).symm ⟨g.val*u.val*g.val⁻¹,hg⟩
  let b := r.right.symm g
  have hqm : (firstCoreEquiv r q).val=g.val*u.val*g.val⁻¹ :=
    congrArg Subtype.val ((firstCoreEquiv r).apply_symm_apply _)
  have hqT : (q:G)∈(T:Subgroup G) := by
    have hQT := pCoreIn_le_sylow H (T.subtype hTH)
    change H.pCoreIn 2≤((T:Subgroup G).subgroupOf H).map H.subtype at hQT
    rw [map_subgroupOf_eq_of_le hTH] at hQT
    exact hQT q.property
  have hqR : r.right ⟨(q:G),hTP hqT⟩=g*r.right ⟨x,hTP hx⟩*g⁻¹ := by
    apply Subtype.ext
    change (r.right ⟨(q:G),hTP hqT⟩).val=g.val*(r.right ⟨x,hTP hx⟩).val*g.val⁻¹
    rw [←marked_endpoint_value r ⟨pCoreIn_le 2 H q.property,hTP hqT⟩,
      ←firstCoreEquiv_val r q,←marked_endpoint_value r ⟨hTH hx,hTP hx⟩]
    exact hqm
  have hqB : (⟨(q:G),hTP hqT⟩:secondParabolic T M Mc H)=b*⟨x,hTP hx⟩*b⁻¹ := by
    apply r.right.injective
    simpa only [b,map_mul,map_inv,r.right.apply_symm_apply] using hqR
  refine ⟨b,q,congrArg Subtype.val hqB,?_⟩
  simpa only [b,r.right.apply_symm_apply] using hqm


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

/-- Ambient fusion back into the full original Sylow has long-root model
image, under the same first endpoint marking and including cubic Mc. -/
theorem source_sylow_fusion_isLongRoot (r : MarkedTriality T M Mc H)
    {x z : G} (hx : x∈(T:Subgroup G)) (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z x) :
    IsLongRootInvolution 1 Nat.zero_lt_one (r.left ⟨x,hH.1.1.2 hx⟩).val := by
  have hzsq : z^2=1 := by
    have hh := pow_card_eq_one' (x := (⟨z,hz⟩:centralInvolutions T))
    rw [plane_centralInvolutions_card T M hM.1.2 hcard e] at hh
    exact congrArg (fun u : centralInvolutions T => (u:G)) hh
  have hxsq : x^2=1 := by
    obtain ⟨a,ha⟩ := isConj_iff.mp hconj
    rw [←ha,conj_pow,hzsq,mul_one,mul_inv_cancel]
  obtain ⟨b,q,hq,hqm⟩ := marked_sylow_square_placement r hH.1.1.2 hx hxsq
  have hqconj : IsConj z (q:G) := hconj.trans (isConj_iff.mpr ⟨(b:G),hq.symm⟩)
  have hlong := source_core_fusion_isLongRoot hG hempty hM hu hmany hcard e hH r q hz hz1 hqconj
  exact hlong.of_isConj 1 Nat.zero_lt_one (isConj_iff.mpr ⟨(r.right b).val,hqm.symm⟩).symm

/-- The same original second-parabolic conjugator puts every returning Sylow
involution in a core quotient orbit of size at most nine. -/
theorem source_sylow_fusion_core_bound (r : MarkedTriality T M Mc H)
    {x z : G} (hx : x∈(T:Subgroup G)) (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z x) :
    ∃ b : secondParabolic T M Mc H, ∃ q : H.pCoreIn 2,
      (q:G)=(b:G)*x*(b:G)⁻¹ ∧
      (firstCoreEquiv r q).val=(r.right b).val*(r.left ⟨x,hH.1.1.2 hx⟩).val*(r.right b).val⁻¹ ∧
      IsLongRootInvolution 1 Nat.zero_lt_one (firstCoreEquiv r q).val ∧
      (ArmsOrbit.points (ArmsOrbit.point (firstCoreEquiv r q))).ncard≤9 := by
  have hzsq : z^2=1 := by
    have hh := pow_card_eq_one' (x := (⟨z,hz⟩:centralInvolutions T))
    rw [plane_centralInvolutions_card T M hM.1.2 hcard e] at hh
    exact congrArg (fun u : centralInvolutions T => (u:G)) hh
  have hxsq : x^2=1 := by
    obtain ⟨a,ha⟩ := isConj_iff.mp hconj
    rw [←ha,conj_pow,hzsq,mul_one,mul_inv_cancel]
  obtain ⟨b,q,hq,hqm⟩ := marked_sylow_square_placement r hH.1.1.2 hx hxsq
  have hc := hconj.trans (isConj_iff.mpr ⟨(b:G),hq.symm⟩)
  exact ⟨b,q,hq,hqm,
    source_core_fusion_isLongRoot hG hempty hM hu hmany hcard e hH r q hz hz1 hc,
    source_core_fusion_orbit_bound hG hempty hM hu hmany hcard e hH r q hz hz1 hc⟩

/-- Returning ambient conjugates throughout the original first endpoint have
long-root images, with its literal marking retained. -/
theorem source_first_fusion_isLongRoot (r : MarkedTriality T M Mc H)
    (x : H) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z (x:G)) :
    IsLongRootInvolution 1 Nat.zero_lt_one (r.left x).val := by
  have hzsq : z^2=1 := by
    have hh := pow_card_eq_one' (x := (⟨z,hz⟩:centralInvolutions T))
    rw [plane_centralInvolutions_card T M hM.1.2 hcard e] at hh
    exact congrArg (fun u : centralInvolutions T => (u:G)) hh
  have hxsq : x^2=1 := by
    apply Subtype.ext
    obtain ⟨a,ha⟩ := isConj_iff.mp hconj
    change (x:G)^2=1
    rw [←ha,conj_pow,hzsq,mul_one,mul_inv_cancel]
  obtain ⟨a,ha⟩ := square_conjugate_into_sylow (T.subtype hH.1.1.2) x hxsq
  let y : H := a*x*a⁻¹
  have hy : (y:G)∈(T:Subgroup G) := ha
  have hcy : IsConj z (y:G) := hconj.trans (isConj_iff.mpr ⟨(a:G),rfl⟩)
  have hl := source_sylow_fusion_isLongRoot hG hempty hM hu hmany hcard e hH r hy hz hz1 hcy
  change IsLongRootInvolution 1 Nat.zero_lt_one (r.left y).val at hl
  apply hl.of_isConj 1 Nat.zero_lt_one
  apply IsConj.symm
  exact (((parabolic P .arms).subtype.comp r.left.toMonoidHom).map_isConj
    (isConj_iff.mpr ⟨a,rfl⟩ : IsConj x y))

/-- The same fusion control holds throughout the second original endpoint;
it uses the commuting overlap square rather than a new marking. -/
theorem source_second_fusion_isLongRoot (r : MarkedTriality T M Mc H)
    (x : secondParabolic T M Mc H) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z (x:G)) :
    IsLongRootInvolution 1 Nat.zero_lt_one (r.right x).val := by
  have hTP : (T:Subgroup G)≤secondParabolic T M Mc H := le_sup_right.trans le_sup_left
  have hzsq : z^2=1 := by
    have hh := pow_card_eq_one' (x := (⟨z,hz⟩:centralInvolutions T))
    rw [plane_centralInvolutions_card T M hM.1.2 hcard e] at hh
    exact congrArg (fun u : centralInvolutions T => (u:G)) hh
  have hxsq : x^2=1 := by
    apply Subtype.ext
    obtain ⟨a,ha⟩ := isConj_iff.mp hconj
    change (x:G)^2=1
    rw [←ha,conj_pow,hzsq,mul_one,mul_inv_cancel]
  obtain ⟨a,ha⟩ := square_conjugate_into_sylow (T.subtype hTP) x hxsq
  let y : secondParabolic T M Mc H := a*x*a⁻¹
  have hy : (y:G)∈(T:Subgroup G) := ha
  have hcy : IsConj z (y:G) := hconj.trans (isConj_iff.mpr ⟨(a:G),rfl⟩)
  have hl := source_sylow_fusion_isLongRoot hG hempty hM hu hmany hcard e hH r hy hz hz1 hcy
  rw [marked_endpoint_value r ⟨hH.1.1.2 hy,y.property⟩] at hl
  change IsLongRootInvolution 1 Nat.zero_lt_one (r.right y).val at hl
  apply hl.of_isConj 1 Nat.zero_lt_one
  apply IsConj.symm
  exact (((parabolic P .central).subtype.comp r.right.toMonoidHom).map_isConj
    (isConj_iff.mpr ⟨a,rfl⟩ : IsConj x y))
end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
