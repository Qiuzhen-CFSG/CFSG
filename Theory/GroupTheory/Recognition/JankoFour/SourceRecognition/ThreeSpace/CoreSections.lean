module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.QuotientActions
public import Theory.GroupTheory.CentralQuotientAutomorphismFixedDerived
/-!
# The original core sections in the radical module

The point-core images in R/Z(R) have dimension eight, any two distinct
ones meet in dimension four and generate the quotient, and the original
marked triple has zero intersection. Multiplication of its three pair
intersections is an actual direct-product coordinate map onto R/Z(R).
Normalizer conjugation permutes these sections exactly as it acts on Z;
S preserves every one. Every original point core fixes its own section
and acts quadratically on the full quotient.

Trivial action on R/Z(R) fixes R′=Z, so the kernel lies in S. In particular
the original K/R action is faithful. These conclusions use the special
radical and the extraspecial point cores; they do not identify the
three-dimensional factor as dual-natural or the four-dimensional factor
as the natural L₂(4) module. Those tensor-action identifications remain.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), the tensor argument in (4.4), pp.597–598,
DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)

theorem space_le_R (h : IsTypeJ4 z) : d.space ≤ d.R :=
  (d.R_commutator_eq_space h).symm.le.trans d.R.commutator_le_self

theorem center_R_card (h : IsTypeJ4 z) : Nat.card (center d.R) = 8 := by
  rw [←card_map_of_injective d.R.subtype_injective,d.R_center_eq_space h]
  exact d.card

/-- The original point-core section inside the literal R/Z(R). -/
def coreSection (t : G) : Subgroup (d.R ⧸ center d.R) :=
  ((ambientCore t).subgroupOf d.R).map (QuotientGroup.mk' (center d.R))

private theorem center_le_pointCore (h : IsTypeJ4 z) {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) : center d.R ≤ (ambientCore t).subgroupOf d.R := by
  intro r hr
  apply d.contained_in_cores t ht ht1
  change (r : G) ∈ d.space
  rw [←d.R_center_eq_space h]
  exact mem_map_of_mem _ hr

theorem coreSection_comap (h : IsTypeJ4 z) {t : G} (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    (d.coreSection t).comap (QuotientGroup.mk' (center d.R)) =
      (ambientCore t).subgroupOf d.R := by
  apply comap_map_eq_self
  rw [QuotientGroup.ker_mk']
  exact d.center_le_pointCore h ht ht1

private theorem card_section (h : IsTypeJ4 z) (U : Subgroup G) (hUR : U ≤ d.R)
    (hZU : d.space ≤ U) :
    Nat.card ((U.subgroupOf d.R).map (QuotientGroup.mk' (center d.R))) * 8 = Nat.card U := by
  let q := QuotientGroup.mk' (center d.R)
  have hk : q.ker ≤ U.subgroupOf d.R := by
    rw [QuotientGroup.ker_mk']
    intro r hr
    apply hZU
    rw [←d.R_center_eq_space h]
    exact mem_map_of_mem _ hr
  have hh := (q.ker.subgroupOf (U.subgroupOf d.R)).index_mul_card
  change q.ker.relIndex (U.subgroupOf d.R) *
    Nat.card (q.ker.subgroupOf (U.subgroupOf d.R)) = Nat.card (U.subgroupOf d.R) at hh
  rw [relIndex_ker,Nat.card_congr (subgroupOfEquivOfLe hk).toEquiv,
    QuotientGroup.ker_mk',d.center_R_card h,
    Nat.card_congr (subgroupOfEquivOfLe hUR).toEquiv] at hh
  exact hh

private theorem pointCore_intersection {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) : ambientCore t ⊓ d.R = ambientCore t ⊓ d.S := by
  exact le_antisymm (inf_le_inf_left _ inf_le_right)
    (le_inf inf_le_left (d.coreCentralizer_le_R ht ht1))

/-- Every point section has binary dimension eight. -/
theorem coreSection_card (h : IsTypeJ4 z) {t : G} (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    Nat.card (d.coreSection t) = 256 := by
  have hh := d.card_section h (ambientCore t ⊓ d.R) inf_le_right
    (le_inf (d.contained_in_cores t ht ht1) (d.space_le_R h))
  rw [inf_subgroupOf_right] at hh
  change Nat.card (d.coreSection t) * 8 = _ at hh
  rw [d.pointCore_intersection ht ht1,d.coreCentralizer_card h ht ht1] at hh
  omega

theorem coreSection_rank (h : IsTypeJ4 z) {t : G} (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    primeRank 2 (d.coreSection t) = 8 := by
  let := d.R_center_quotient_elementary h
  let : IsElementaryAbelian 2 (d.coreSection t) :=
    IsElementaryAbelian.of_injective (d.coreSection t).subtype (d.coreSection t).subtype_injective
  rw [←IsElementaryAbelian.log_card_eq_primeRank (p := 2),d.coreSection_card h ht ht1]
  norm_num

private theorem point_pair_conj {t u : G} (ht : t ∈ d.space) (hu : u ∈ d.space)
    (ht1 : t ≠ 1) (hu1 : u ≠ 1) : IsConj t u := by
  obtain ⟨a,_,ha⟩ := d.normalizer_transitive t ht ht1
  obtain ⟨b,_,hb⟩ := d.normalizer_transitive u hu hu1
  exact (isConj_iff.mpr ⟨a,ha⟩).symm.trans (isConj_iff.mpr ⟨b,hb⟩)

theorem point_pair_le_R (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u) :
    ambientCore t ⊓ ambientCore u ≤ d.R := by
  let := returningIntersection_elementary (d.point_type h ht ht1)
    (d.point_pair_conj ht hu ht1 hu1) htu.symm
  apply (le_inf inf_le_left ?_).trans (d.coreCentralizer_le_R ht ht1)
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm
    (⟨y,d.contained_in_cores t ht ht1 hy,d.contained_in_cores u hu hu1 hy⟩ :
      (ambientCore t ⊓ ambientCore u : Subgroup G)) (⟨x,hx⟩ : (ambientCore t ⊓ ambientCore u : Subgroup G)))

/-- Intersection of the two literal quotient sections is the quotient of the two cores. -/
theorem coreSection_inf (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (ht1 : t ≠ 1) (hu1 : u ≠ 1) :
    d.coreSection t ⊓ d.coreSection u =
      ((ambientCore t ⊓ ambientCore u).subgroupOf d.R).map (QuotientGroup.mk' (center d.R)) := by
  apply comap_injective (QuotientGroup.mk'_surjective (center d.R))
  rw [comap_inf,d.coreSection_comap h ht ht1,d.coreSection_comap h hu hu1,
    comap_map_eq_self]
  · rfl
  · rw [QuotientGroup.ker_mk']
    exact le_inf (d.center_le_pointCore h ht ht1) (d.center_le_pointCore h hu hu1)

/-- Distinct point sections meet in a binary four-space. -/
theorem coreSection_inf_card (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u) :
    Nat.card (d.coreSection t ⊓ d.coreSection u : Subgroup (d.R ⧸ center d.R)) = 16 := by
  rw [d.coreSection_inf h ht hu ht1 hu1]
  have hh := d.card_section h (ambientCore t ⊓ ambientCore u)
    (d.point_pair_le_R h ht hu ht1 hu1 htu)
    (le_inf (d.contained_in_cores t ht ht1) (d.contained_in_cores u hu hu1))
  rw [(returning_intersection_image_orders (d.point_type h ht ht1)
    (d.point_pair_conj ht hu ht1 hu1) (d.contained_in_cores t ht ht1 hu) htu.symm).1] at hh
  omega

/-- Every pair of distinct point sections generates the entire quotient. -/
theorem coreSection_sup (h : IsTypeJ4 z) {t u : G}
    (ht : t ∈ d.space) (hu : u ∈ d.space) (ht1 : t ≠ 1) (hu1 : u ≠ 1) (htu : t ≠ u) :
    d.coreSection t ⊔ d.coreSection u = ⊤ := by
  have he (v : G) (hv : v ∈ d.space) (hv1 : v ≠ 1) :
      (ambientCore v).subgroupOf d.R = (ambientCore v ⊓ d.S).subgroupOf d.R := by
    ext r
    exact ⟨fun hr => ⟨hr,r.property.2⟩,fun hr => hr.1⟩
  change ((ambientCore t).subgroupOf d.R).map _ ⊔ ((ambientCore u).subgroupOf d.R).map _ = _
  rw [←Subgroup.map_sup,he t ht ht1,he u hu hu1,
    ←subgroupOf_sup (d.coreCentralizer_le_R ht ht1) (d.coreCentralizer_le_R hu hu1),
    ←d.R_eq_pointCore_join h ht hu ht1 hu1 htu,subgroupOf_self,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

/-- The quotient action fixes a representative exactly when its original commutator lies in Z. -/
theorem radicalAction_mk_fixed_iff (h : IsTypeJ4 z)
    (n : normalizer (d.space : Set G)) (r : d.R) :
    d.radicalAction n (QuotientGroup.mk' (center d.R) r) = QuotientGroup.mk' (center d.R) r ↔
      ⁅(n : G),(r : G)⁆ ∈ d.space := by
  rw [d.radicalAction_mk]
  change ((⟨(n : G)*(r : G)*(n : G)⁻¹,_⟩ : d.R) : d.R ⧸ center d.R) =
    (r : d.R ⧸ center d.R) ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  have hm (x : d.R) : x ∈ center d.R ↔ (x : G) ∈ d.space := by
    rw [←d.R_center_eq_space h]
    exact (mem_map_iff_mem d.R.subtype_injective).symm
  rw [hm]
  simp only [div_eq_mul_inv,Subgroup.coe_mul,Subgroup.coe_inv,commutatorElement_def]

private theorem pointCore_commutator_le (h : IsTypeJ4 z) {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) : ⁅ambientCore t,ambientCore t⁆ ≤ d.space := by
  let ht' := d.point_type h ht ht1
  let := IsExtraspecial.of_mulEquiv (LocalGeometry.coreEquivAmbient t) ht'.extraspecial
  rw [←map_subtype_commutator,IsExtraspecial.commutator_eq_center (p := 2),
    LocalGeometry.ambientCore_center_image ht']
  exact zpowers_le.mpr ht

/-- Each original point core fixes its entire eight-dimensional radical section. -/
theorem pointCore_fixes_coreSection (h : IsTypeJ4 z) {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) (q : ambientCore t)
    {v : d.R ⧸ center d.R} (hv : v ∈ d.coreSection t) :
    d.radicalAction (inclusion (d.cores_normalize t ht ht1) q) v = v := by
  obtain ⟨r,hr,rfl⟩ := hv
  apply (d.radicalAction_mk_fixed_iff h _ r).mpr
  exact d.pointCore_commutator_le h ht ht1 (commutator_mem_commutator q.property hr)

/-- The full point core acts quadratically on R/Z, in the original conjugation convention. -/
theorem pointCore_quadratic_commutator (h : IsTypeJ4 z) {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) :
    ⁅ambientCore t,⁅ambientCore t,d.R⁆⁆ ≤ d.space := by
  have hRQ : d.R ≤ normalizer (ambientCore t : Set G) := by
    rw [LocalGeometry.normalizer_ambientCore (d.point_type h ht ht1)]
    exact inf_le_right.trans (d.S_le_point_centralizer ht)
  exact (commutator_mono le_rfl (le_normalizer_iff_commutator_le_left.mp hRQ)).trans
    (d.pointCore_commutator_le h ht ht1)

set_option backward.isDefEq.respectTransparency false in
/-- The same quadratic statement for the actual quotient automorphisms. -/
theorem pointCore_quadratic_action (h : IsTypeJ4 z) {t : G}
    (ht : t ∈ d.space) (ht1 : t ≠ 1) (a b : ambientCore t) (v : d.R ⧸ center d.R) :
    d.radicalAction (inclusion (d.cores_normalize t ht ht1) a)
      (d.radicalAction (inclusion (d.cores_normalize t ht ht1) b) v * v⁻¹) =
      d.radicalAction (inclusion (d.cores_normalize t ht ht1) b) v * v⁻¹ := by
  obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (center d.R) v
  rw [d.radicalAction_mk,←map_inv,←map_mul]
  apply (d.radicalAction_mk_fixed_iff h _ _).mpr
  exact d.pointCore_quadratic_commutator h ht ht1
    (commutator_mem_commutator a.property (commutator_mem_commutator b.property r.property))

private theorem coreSection_conjugate_le (n : normalizer (d.space : Set G)) (t : G) :
    (d.coreSection t).map (d.radicalAction n).toMonoidHom ≤
      d.coreSection ((n : G)*t*(n : G)⁻¹) := by
  rintro _ ⟨v,⟨r,hr,rfl⟩,rfl⟩
  rw [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,d.radicalAction_mk]
  refine mem_map_of_mem (QuotientGroup.mk' (center d.R)) ?_
  change (n : G)*(r : G)*(n : G)⁻¹ ∈ ambientCore ((n : G)*t*(n : G)⁻¹)
  change _ ∈ ambientCore ((MulAut.conj (n : G)) t)
  rw [←ambientCore_map (MulAut.conj (n : G)) t]
  exact mem_map_of_mem _ hr

/-- Conjugation carries the actual point sections with the original action on Z. -/
theorem coreSection_conjugate (n : normalizer (d.space : Set G)) (t : G) :
    (d.coreSection t).map (d.radicalAction n).toMonoidHom =
      d.coreSection ((n : G)*t*(n : G)⁻¹) := by
  apply eq_of_le_of_card_ge (d.coreSection_conjugate_le n t)
  rw [card_map_of_injective (d.radicalAction n).injective]
  have hh := card_le_of_le (d.coreSection_conjugate_le n⁻¹ ((n : G)*t*(n : G)⁻¹))
  rw [card_map_of_injective (d.radicalAction n⁻¹).injective] at hh
  simpa only [Subgroup.coe_inv,inv_inv,inv_mul_cancel_left,mul_inv_cancel_right,
    mul_assoc,inv_mul_cancel,mul_one] using hh

/-- The original S-factor preserves every point section. -/
theorem coreSection_S_invariant {t : G} (ht : t ∈ d.space) (s : d.S) :
    (d.coreSection t).map
      (d.radicalAction (inclusion (centralizer_le_normalizer _) s)).toMonoidHom = d.coreSection t := by
  rw [d.coreSection_conjugate]
  have he : (s : G)*t*(s : G)⁻¹ = t := by
    rw [←s.property t ht,mul_inv_cancel_right]
  exact congrArg d.coreSection he

/-- Trivial action on R/Z fixes R′=Z, so the action kernel lies in the original S. -/
theorem radicalAction_ker_le_S (h : IsTypeJ4 z) :
    d.radicalAction.ker ≤ d.S.subgroupOf (normalizer (d.space : Set G)) := by
  intro n hn t ht
  let a : MulAut d.R := d.R.normalizerMonoidHom (inclusion d.R_normalized n)
  have ha : quotientAut (center d.R) a = 1 := hn
  have hf := MulAut.fixes_commutator_of_quotientCenter_eq_one a ha
  rw [d.R_derived_eq_center h] at hf
  rw [←d.R_center_eq_space h] at ht
  obtain ⟨r,hr,rfl⟩ := ht
  have he := congrArg Subtype.val ((MulAut.mem_fixedSubgroup a r).mp (hf hr))
  change (n : G)*(r : G)*(n : G)⁻¹ = (r : G) at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

attribute [local instance] R_normal_in_K

/-- The original K/R acts faithfully on the radical quotient. -/
theorem KRadicalAction_injective (h : IsTypeJ4 z) : Function.Injective (d.KRadicalAction h) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (d.R.subgroupOf d.K) a
  have hk : inclusion d.K_le_normalizer k ∈ d.radicalAction.ker := ha
  have hs := d.radicalAction_ker_le_S h hk
  apply mem_bot.mpr
  exact (QuotientGroup.eq_one_iff _).mpr ⟨k.property,hs⟩

private theorem marked_points (h : IsTypeJ4 z) :
    z ∈ d.space ∧ d.r ∈ d.space ∧ d.s ∈ d.space ∧ z ≠ 1 ∧ d.r ≠ 1 ∧ d.s ≠ 1 := by
  have hz1 : z ≠ 1 := by intro he; have hi := h.involution; simp [he] at hi
  refine ⟨?_,?_,?_,hz1,?_,?_⟩
  · rw [space,d.generated]; exact subset_closure (by simp)
  · rw [space,d.generated]; exact subset_closure (by simp)
  · rw [space,d.generated]; exact subset_closure (by simp)
  · intro he; exact hz1 (isConj_one_left.mp (he ▸ d.r_conj))
  · intro he; exact hz1 (isConj_one_left.mp (he ▸ d.s_conj))

/-- The marked triple of source cores has trivial intersection modulo Z. -/
theorem coreSection_triple_inf (h : IsTypeJ4 z) :
    d.coreSection z ⊓ d.coreSection d.r ⊓ d.coreSection d.s = ⊥ := by
  obtain ⟨hz,hr,hs,hz1,hr1,hs1⟩ := d.marked_points h
  apply comap_injective (QuotientGroup.mk'_surjective (center d.R))
  rw [comap_inf,comap_inf,d.coreSection_comap h hz hz1,d.coreSection_comap h hr hr1,
    d.coreSection_comap h hs hs1,MonoidHom.comap_bot,QuotientGroup.ker_mk']
  change d.space.subgroupOf d.R = center d.R
  rw [←d.R_center_eq_space h,←comap_subtype,comap_map_eq_self_of_injective d.R.subtype_injective]

private theorem triple_product_injective {V : Type*} [Group V] [IsMulCommutative V]
    (A B C : Subgroup V) (hzero : A ⊓ B ⊓ C = ⊥) :
    Function.Injective ((A ⊓ B).subtype.coprod ((A ⊓ C).subtype.coprod (B ⊓ C).subtype)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  rintro ⟨a,b,c⟩ habc
  have he : (a : V)*((b : V)*(c : V))=1 := habc
  have haC : (a : V) ∈ C := by
    have he' : (a : V) = ((b : V)*(c : V))⁻¹ := eq_inv_of_mul_eq_one_left he
    rw [he']
    exact C.inv_mem (C.mul_mem b.property.2 c.property.2)
  have ha : (a : V)=1 := mem_bot.mp (hzero ▸ (show (a : V) ∈ A ⊓ B ⊓ C from ⟨a.property,haC⟩))
  have hbc : (b : V)*(c : V)=1 := by simpa only [ha,one_mul] using he
  have hbB : (b : V) ∈ B := by
    rw [eq_inv_of_mul_eq_one_left hbc]
    exact B.inv_mem c.property.1
  have hb : (b : V)=1 := mem_bot.mp (hzero ▸
    (show (b : V) ∈ A ⊓ B ⊓ C from ⟨⟨b.property.1,hbB⟩,b.property.2⟩))
  have hc : (c : V)=1 := by simpa only [hb,one_mul] using hbc
  exact mem_bot.mpr (Prod.ext (Subtype.ext ha) (Prod.ext (Subtype.ext hb) (Subtype.ext hc)))

/-- Multiplication of the three original pair sections is a direct-product
coordinate system on R/Z. Each factor has order sixteen. -/
theorem exists_coreSection_product (h : IsTypeJ4 z) :
    ∃ f : (d.coreSection z ⊓ d.coreSection d.r : Subgroup (d.R ⧸ center d.R)) ×
      ((d.coreSection z ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R)) ×
        (d.coreSection d.r ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R))) ≃*
          (d.R ⧸ center d.R),
      ∀ a b c, f (a,b,c) = (a : d.R ⧸ center d.R)*((b : d.R ⧸ center d.R)*(c : d.R ⧸ center d.R)) := by
  let := d.R_center_quotient_elementary h
  obtain ⟨hz,hr,hs,hz1,hr1,hs1⟩ := d.marked_points h
  let f := (d.coreSection z ⊓ d.coreSection d.r).subtype.coprod
    ((d.coreSection z ⊓ d.coreSection d.s).subtype.coprod
      (d.coreSection d.r ⊓ d.coreSection d.s).subtype)
  have hf : Function.Bijective f := by
    apply (Nat.bijective_iff_injective_and_card f).mpr
    refine ⟨triple_product_injective _ _ _ (d.coreSection_triple_inf h),?_⟩
    rw [Nat.card_prod,Nat.card_prod,d.coreSection_inf_card h hz hr hz1 hr1 d.r_ne.symm,
      d.coreSection_inf_card h hz hs hz1 hs1 d.s_ne.symm,
      d.coreSection_inf_card h hr hs hr1 hs1 d.distinct,d.R_center_quotient_card h]
  exact ⟨MulEquiv.ofBijective f hf,fun _ _ _ => rfl⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
end
