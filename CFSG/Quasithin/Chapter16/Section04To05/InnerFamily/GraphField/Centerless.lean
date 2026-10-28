module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.ModelData
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowImageIntersection

/-!
# The centerless graph-field complement

For the prepared choices of 16.4.9, the saturated normalizer gives the
Sylow centralizer of the marked four-group. Conjugating the actual complement
inside that centralizer preserves the marked Frattini product. Its intersection
with the opposite centralizer is trivial, so its image in the relative quotient
is quaternion. The intrinsic quaternion placement then lifts through the
opposite Sylow subgroup and gives the contradiction of source (+).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1191–1192. The intrinsic normalizer and quaternion placement remain inputs.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField.Centerless
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

omit [Finite G] in
private theorem four_centralizer_le_z :
    centralizer (fourGroup r z : Set G) ≤ centralizer ({z} : Set G) := by
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (hx z (mem_sup_right (mem_zpowers z))).symm

omit [Finite G] in
private theorem four_centralizer_le_r :
    centralizer (fourGroup r z : Set G) ≤ centralizer ({r} : Set G) := by
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (hx r (mem_sup_left (mem_zpowers r))).symm

/-- Tight embedding puts the full marked centralizer in N_G(L). -/
theorem centralizer_z_le_normalizer (h : IntersectionSetup T z L g R) :
    centralizer ({z} : Set G) ≤ normalizer (L : Set G) := by
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, h.involution, pow_one])
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  have hn := h.tight.normalizer_le hp (zpowers_ne_bot.mpr hz1)
    (zpowers_le.mpr (central_involution_mem_centralizer h))
  rwa [h.normalizers_eq, normalizer_zpowers_eq_centralizer_of_order_two z h.involution] at hn

private theorem r_powers (h : IntersectionSetup T z L g R)
    (hsmall : OrderTwoOutsideDeltaZero L) (hempty : ¬ (deltaZero L).Nonempty)
    (hr : r ∈ R) (hr2 : orderOf r = 2) : zpowers r = R := by
  have hc := hsmall _ h.mem_delta (fun hm => hempty ⟨_, hm⟩) R h.sylow
  exact eq_of_le_of_card_ge (zpowers_le.mpr hr) (by rw [Nat.card_zpowers, hr2, hc])

/-- Exact 16.4.2(6) specialized to R=⟨r⟩. The Sylow hypothesis is in
N_H(R), not in the ambient normalizer N_G(R). -/
theorem four_centralizer_sylow (h : IntersectionSetup T z L g R)
    (hR : zpowers r = R) (hr2 : orderOf r = 2)
    (hsat : SylowIn ((T : Subgroup G) ⊓ normalizer (R : Set G))
      (normalizer (L : Set G) ⊓ normalizer (R : Set G))) :
    SylowIn ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
      (centralizer (fourGroup r z : Set G)) := by
  have hnR : normalizer (R : Set G) = centralizer ({r} : Set G) := by
    rw [← hR, normalizer_zpowers_eq_centralizer_of_order_two r hr2]
  have heq : (T : Subgroup G) ⊓ normalizer (R : Set G) =
      (T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G) := by
    rw [hnR]
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1, ?_⟩
      have hf : fourGroup r z ≤ centralizer ({x} : Set G) := by
        apply sup_le <;> apply zpowers_le.mpr
        · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hx.2).symm
        · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (h.sylow_centralizes hx.1)).symm
      intro y hy
      exact mem_centralizer_singleton_iff.mp (hf hy)
    · exact inf_le_inf_left _ four_centralizer_le_r
  have hc : centralizer (fourGroup r z : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (R : Set G) := by
    rw [hnR]
    exact le_inf (four_centralizer_le_z.trans (centralizer_z_le_normalizer h)) four_centralizer_le_r
  have hp := T.isPGroup'.to_inf_left (K := centralizer (fourGroup r z : Set G))
  obtain ⟨S, hS⟩ := (hp.of_equiv (subgroupOfEquivOfLe inf_le_right).symm).exists_le_sylow
  refine ⟨S, ?_⟩
  apply Eq.trans (hsat.maximal (S.isPGroup'.map _) ((map_subtype_le _).trans hc) ?_) heq
  rw [heq, ← map_subgroupOf_eq_of_le (show (T : Subgroup G) ⊓
    centralizer (fourGroup r z : Set G) ≤ centralizer (fourGroup r z : Set G) from inf_le_right)]
  exact map_mono hS

/-- The central mark is outer on L′ in the contrary empty-family case. -/
theorem z_outside_conjugate_product (h : IntersectionSetup T z L g R)
    (hsmall : OrderTwoOutsideDeltaZero L) (hempty : ¬ (deltaZero L).Nonempty)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L) :
    z ∉ centralizer (L.conjBy g : Set G) ⊔ L.conjBy g := by
  have hC : (centralizer (L : Set G)).conjBy g = centralizer (L.conjBy g : Set G) :=
    map_centralizer_equiv _ (MulAut.conj g)
  have hzK : z ∈ centralizer (L : Set G) := central_involution_mem_centralizer h
  have hznot : z ∉ centralizer (L.conjBy g : Set G) := by
    intro hz
    have hzR : z ∈ R := h.eq_intersection.symm ▸ ⟨hC.symm ▸ hz, h.mem_sylow⟩
    have he := h.sylow.involution_eq_of_commute_of_card_two
      (hsmall _ h.mem_delta (fun hm => hempty ⟨_, hm⟩) R h.sylow)
      hr hr2 (h.sylow.le hzR) h.involution
      (mem_centralizer_singleton_iff.mp (h.sylow_centralizes (h.le_sylow hr)))
    exact hout (mem_sup_left (he ▸ hzK))
  intro hz
  have hd := mem_deltaZero_of_inner_involution (normalizers_eq_conjBy h.normalizers_eq g)
    (hsmall.conjBy g) (J := centralizer (L : Set G))
    ⟨g⁻¹, by rw [← hC, conjBy_inv]⟩ hzK h.involution hz hznot
  exact hempty ((deltaZero_conjBy_nonempty_iff g).mp ⟨_, hd⟩)


private theorem conjugate_into_sylow {S A H : Subgroup G} (hs : SylowIn S H)
    (ha : IsPGroup 2 A) (hle : A ≤ H) : ∃ a ∈ H, A.conjBy a ≤ S := by
  obtain ⟨U, hU⟩ := (ha.of_equiv (subgroupOfEquivOfLe hle).symm).exists_le_sylow
  obtain ⟨a, ha, he⟩ := (show SylowIn ((U : Subgroup H).map H.subtype) H from
    ⟨U, rfl⟩).exists_conjugator hs
  refine ⟨a, ha, ?_⟩
  rw [← he]
  apply map_mono
  rw [← map_subgroupOf_eq_of_le hle]
  exact map_mono hU

omit [Finite G] in
private theorem fixes_of_centralizes {a x : G}
    (ha : a ∈ centralizer ({x} : Set G)) : MulAut.conj a x = x := by
  change a * x * a⁻¹ = x
  rw [mem_centralizer_singleton_iff.mp ha, mul_inv_cancel_right]

/-- A choice inside C_G(E) puts the whole Q, hence its actual complement,
inside C_T(E). The complement and its marked Frattini product are transported. -/
theorem exists_complement_in_sylow_centralizer (h : IntersectionSetup T z L g R)
    (d : NormalizerData L r z) (c : CenterlessComplementData d)
    (hs : SylowIn ((T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
      (centralizer (fourGroup r z : Set G))) :
    ∃ a ∈ centralizer (fourGroup r z : Set G),
      d.Q.conjBy a ≤ (T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G) ∧
      c.P.conjBy a ≤ d.Q.conjBy a ∧
      Disjoint (c.P.conjBy a) (fourGroup r z) ∧
      c.P.conjBy a ⊔ fourGroup r z = d.Q.conjBy a ∧
      Nonempty (c.P.conjBy a ≃* QuaternionGroup 2) ∧
      IsPGroup 2 (c.P.conjBy a) ∧
      ∃ v ∈ (frattini (c.P.conjBy a)).map (c.P.conjBy a).subtype,
        orderOf v = 2 ∧ v ∈ L ⊓ centralizer ({r} : Set G) ∧
        ∃ l ∈ L, MulAut.conj l r = r * v := by
  obtain ⟨a, ha, hQa⟩ := conjugate_into_sylow hs d.two_group c.centralizes_four
  let e := MulAut.conj a
  have har : e r = r := fixes_of_centralizes (four_centralizer_le_r ha)
  have haz : e z = z := fixes_of_centralizes (four_centralizer_le_z ha)
  have hEa : (fourGroup r z).conjBy a = fourGroup r z := by
    change (zpowers r ⊔ zpowers z).map e.toMonoidHom = _
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    change zpowers (e r) ⊔ zpowers (e z) = _
    rw [har, haz]
    rfl
  have haL : a ∈ normalizer (L : Set G) :=
    centralizer_z_le_normalizer h (four_centralizer_le_z ha)
  have hLa : L.conjBy a = L := mem_normalizer_iff_map_conj_eq.mp haL
  have hdis : Disjoint (c.P.conjBy a) (fourGroup r z) := by
    rw [disjoint_iff, ← hEa]
    change c.P.map e.toMonoidHom ⊓ (fourGroup r z).map e.toMonoidHom = ⊥
    rw [← map_inf _ _ _ e.injective, c.disjoint_four.eq_bot, Subgroup.map_bot]
  have hsup : c.P.conjBy a ⊔ fourGroup r z = d.Q.conjBy a := by
    rw [← hEa]
    change c.P.map e.toMonoidHom ⊔ (fourGroup r z).map e.toMonoidHom = d.Q.map e.toMonoidHom
    rw [← Subgroup.map_sup, c.sup_four]
  obtain ⟨eqv⟩ := c.quaternion
  refine ⟨a, ha, hQa, map_mono c.le_Q, hdis, hsup,
    ⟨(e.subgroupMap c.P).symm.trans eqv⟩,
    (d.two_group.to_le c.le_Q).map e.toMonoidHom, ?_⟩
  obtain ⟨v, ⟨vP, hvP, rfl⟩, hv2, hvL, l, hl, hprod⟩ := c.frattini_product
  change orderOf (vP : G) = 2 at hv2
  change (vP : G) ∈ L ⊓ centralizer ({r} : Set G) at hvL
  change MulAut.conj l r = r * (vP : G) at hprod
  let f := e.subgroupMap c.P
  have hfv : f vP ∈ frattini (c.P.conjBy a) :=
    frattini_le_comap_frattini_of_surjective (φ := f.toMonoidHom) f.surjective hvP
  refine ⟨e vP, ⟨f vP, hfv, rfl⟩, (e.orderOf_eq _).trans hv2, ?_, e l, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have hv : e (vP : G) ∈ L.conjBy a := mem_map_of_mem e.toMonoidHom hvL.1
      exact hLa.le hv
    · apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg e (mem_centralizer_singleton_iff.mp hvL.2)
      simpa only [map_mul, har] using hh
  · exact hLa ▸ mem_map_of_mem e.toMonoidHom hl
  · have hh := congrArg e hprod
    simpa only [MulAut.conj_apply, map_mul, map_inv, har] using hh

/-- The actual normalizer inclusion followed by the relative action quotient. -/
def complementProjection {J P : Subgroup G} (hP : P ≤ normalizer (J : Set G)) :
    P →* actionQuotient J := (actionProjection J).comp (inclusion hP)

omit [Finite G] in
/-- Disjointness from the relative kernel proves faithfulness; it is not an input
about the resulting quaternion image. -/
theorem complementProjection_injective {J P : Subgroup G}
    (hn : P ≤ normalizer (J : Set G)) (hd : Disjoint P (centralizer (J : Set G))) :
    Function.Injective (complementProjection hn) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hxK : (x : G) ∈ centralizer (J : Set G) :=
    (QuotientGroup.eq_one_iff (inclusion hn x)).mp hx
  exact Subtype.ext (disjoint_def.mp hd x.property hxK)

omit [Finite G] in
/-- Quotient placement lifts with exactly the restricted centralizer kernel. -/
theorem lift_quaternion_placement {J P : Subgroup G} {s : G}
    (hN : P ≤ normalizer (J : Set G)) (hsN : s ∈ normalizer (J : Set G))
    (hs2 : orderOf s = 2) (hout : s ∉ centralizer (J : Set G) ⊔ J)
    (hd : Disjoint P (centralizer (J : Set G)))
    (he : Nonempty (P ≃* QuaternionGroup 2))
    (hfix : P ≤ centralizer ({s} : Set G)) (hplace : QuaternionPlacement J) :
    P ≤ (centralizer (J : Set G) ⊔ J) ⊔ zpowers s := by
  let H := normalizer (J : Set G)
  let sH : H := ⟨s, hsN⟩
  let q := actionProjection J
  let f := complementProjection hN
  have hf : Function.Injective f := complementProjection_injective hN hd
  obtain ⟨e⟩ := he
  have hQ : Nonempty (f.range ≃* QuaternionGroup 2) :=
    ⟨(MonoidHom.ofInjective hf).symm.trans e⟩
  have hC : f.range ≤ centralizer ({q sH} : Set (actionQuotient J)) := by
    rintro _ ⟨x, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hcomm : inclusion hN x * sH = sH * inclusion hN x :=
      Subtype.ext (mem_centralizer_singleton_iff.mp (hfix x.property))
    exact (q.map_mul _ _).symm.trans ((congrArg q hcomm).trans (q.map_mul _ _))
  have hplaced := hplace sH hs2 hout f.range hQ hC
  intro x hx
  let xP : P := ⟨x, hx⟩
  have hm := hplaced (show f xP ∈ f.range from ⟨xP, rfl⟩)
  have hm' : q (inclusion hN xP) ∈ (J.subgroupOf H ⊔ zpowers sH).map q := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    exact hm
  have hk : inclusion hN xP ∈ (J.subgroupOf H ⊔ zpowers sH) ⊔ q.ker := by
    rw [← Subgroup.comap_map_eq]
    exact hm'
  have hv := mem_map_of_mem H.subtype hk
  rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers,
    map_subgroupOf_eq_of_le J.le_normalizer] at hv
  have hker : q.ker.map H.subtype = centralizer (J : Set G) := by
    rw [show q.ker = (centralizer (J : Set G)).subgroupOf H from QuotientGroup.ker_mk' _,
      map_subgroupOf_eq_of_le (centralizer_le_normalizer _)]
  rw [hker] at hv
  exact (show (J ⊔ zpowers s) ⊔ centralizer (J : Set G) ≤
      (centralizer (J : Set G) ⊔ J) ⊔ zpowers s by
        exact sup_le (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
          (le_sup_left.trans le_sup_left)) hv


/-- In a supplied Sylow subgroup, the intersection with a product of two
normal subgroups is generated by the intersections with the factors. -/
theorem sylow_product_bound {A B D : Subgroup G} (S : Sylow 2 G)
    [A.Normal] [B.Normal] (hA : (S : Subgroup G) ⊓ A ≤ D) (hB : B ≤ D) :
    (S : Subgroup G) ⊓ (A ⊔ B) ≤ D := by
  obtain ⟨U, hU⟩ := S.exists_sylow_map_eq_inf_of_normal A
  let q := QuotientGroup.mk' B
  have he := S.map_image_eq_inf A ((S : Subgroup G) ⊓ A) U hU inf_le_left q
  intro x hx
  have hqx : q x ∈ ((S : Subgroup G) ⊓ A).map q := by
    rw [he]
    refine ⟨mem_map_of_mem q hx.1, ?_⟩
    change q x ∈ A.map q
    have hh := mem_map_of_mem q hx.2
    simp only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at hh
    exact hh
  obtain ⟨a, ha, heq⟩ := hqx
  have hb : a⁻¹ * x ∈ B := by
    apply (QuotientGroup.eq_one_iff (a⁻¹ * x)).mp
    change q (a⁻¹ * x) = 1
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  have hh := D.mul_mem (hA ha) (hB hb)
  simpa only [mul_inv_cancel_left] using hh

/-- The compatible conjugator identifies the complete opposite Sylow kernel
with the marked involution r. It asserts no second interchange. -/
theorem conjugate_sylow_kernel (h : IntersectionSetup T z L g R)
    (hTC : commutingSylow T L = zpowers z)
    (htransport : (T : Subgroup G) ⊓ normalizer
      ((centralizer (L : Set G)).conjBy g : Set G) ≤ (T : Subgroup G).conjBy g)
    (hr : r ∈ R) (hr2 : orderOf r = 2) :
    (T : Subgroup G).conjBy g ⊓ centralizer (L.conjBy g : Set G) = zpowers r := by
  have hz := compatible_conjugator_sends_z h hTC htransport hr hr2
  have hC : (centralizer (L : Set G)).conjBy g = centralizer (L.conjBy g : Set G) :=
    map_centralizer_equiv _ (MulAut.conj g)
  rw [← hC]
  change (T : Subgroup G).map (MulAut.conj g).toMonoidHom ⊓
    (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom = _
  rw [← map_inf _ _ _ (MulAut.conj g).injective]
  change (commutingSylow T L).map (MulAut.conj g).toMonoidHom = _
  rw [hTC, MonoidHom.map_zpowers]
  exact congrArg zpowers hz

/-- The entire source intersection Tᵍ ∩ K′L′E lies in L′E. Both normal
subgroups in the calculation are restricted to H′ before using quotients. -/
theorem conjugate_sylow_product_le (h : IntersectionSetup T z L g R)
    (hTC : commutingSylow T L = zpowers z)
    (htransport : (T : Subgroup G) ⊓ normalizer
      ((centralizer (L : Set G)).conjBy g : Set G) ≤ (T : Subgroup G).conjBy g)
    (hr : r ∈ R) (hr2 : orderOf r = 2) :
    (T : Subgroup G).conjBy g ⊓
      ((centralizer (L.conjBy g : Set G) ⊔ L.conjBy g) ⊔ fourGroup r z) ≤
      L.conjBy g ⊔ fourGroup r z := by
  let J := L.conjBy g
  let H := normalizer (J : Set G)
  let K := centralizer (J : Set G)
  let S := T.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hSH : (S : Subgroup G) ≤ H := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) h.sylow_normalizes
    rwa [map_equiv_normalizer_eq] at hh
  let S₀ := S.subtype hSH
  let K₀ := K.subgroupOf H
  let J₀ := J.subgroupOf H
  have hKH : K ≤ H := centralizer_le_normalizer _
  have hJH : J ≤ H := J.le_normalizer
  let : K₀.Normal := normal_subgroupOf_centralizer_normalizer (J : Set G)
  let : J₀.Normal := normal_in_normalizer
  have hker := conjugate_sylow_kernel h hTC htransport hr hr2
  have hEH : fourGroup r z ≤ H := fourGroup_le_conjugate_normalizer h hr hr2
  have hES : fourGroup r z ≤ (S : Subgroup G) := by
    apply htransport.trans' (le_inf (fourGroup_le_sylow h hr) ?_)
    rw [show (centralizer (L : Set G)).conjBy g = centralizer (L.conjBy g : Set G) from
      map_centralizer_equiv _ (MulAut.conj g), normalizers_eq_conjBy h.normalizers_eq g]
    exact hEH
  have hbound : (S : Subgroup G) ⊓ (K ⊔ J) ≤ J ⊔ fourGroup r z := by
    have hb := sylow_product_bound (A := K₀) (B := J₀)
      (D := (J ⊔ fourGroup r z).subgroupOf H) S₀
      (by
        intro x hx
        have hm : (x : G) ∈ (S : Subgroup G) ⊓ K := ⟨hx.1, hx.2⟩
        have hm' : (x : G) ∈ zpowers r := hker.le hm
        exact mem_sup_right (mem_sup_left hm'))
      (fun _ hx => mem_sup_left hx)
    intro x hx
    have hxH := hSH hx.1
    have hm : (⟨x, hxH⟩ : H) ∈ K₀ ⊔ J₀ := by
      rw [← subgroupOf_sup hKH hJH]
      exact hx.2
    exact hb ⟨hx.1, hm⟩
  have hEn : fourGroup r z ≤ normalizer ((K ⊔ J : Subgroup G) : Set G) := by
    apply le_trans hEH
    exact (le_inf (normalizer_le_normalizer_centralizer J) le_rfl).trans
      (normalizer_inf_normalizer_le_normalizer_sup K J)
  intro x hx
  have hxprod : x ∈ ((K ⊔ J : Subgroup G) : Set G) * (fourGroup r z : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hEn]
    exact hx.2
  obtain ⟨u, hu, e, he, hue⟩ := hxprod
  have huS : u ∈ (S : Subgroup G) := by
    have hh := (S : Subgroup G).mul_mem hx.1 ((S : Subgroup G).inv_mem (hES he))
    rwa [← hue, mul_inv_cancel_right] at hh
  rw [← hue]
  exact (J ⊔ fourGroup r z).mul_mem (hbound ⟨huS, hu⟩) (mem_sup_right he)


/-- Faithfulness in H′/K′ follows from the actual Sylow intersection R=⟨r⟩
and from the complement's disjointness from E. -/
theorem placed_complement_disjoint_kernel (h : IntersectionSetup T z L g R)
    (hR : zpowers r = R) {P : Subgroup G} (hPT : P ≤ (T : Subgroup G))
    (hd : Disjoint P (fourGroup r z)) : Disjoint P (centralizer (L.conjBy g : Set G)) := by
  apply disjoint_def.mpr
  intro x hx hxK
  have hC : (centralizer (L : Set G)).conjBy g = centralizer (L.conjBy g : Set G) :=
    map_centralizer_equiv _ (MulAut.conj g)
  have hxR : x ∈ R := h.eq_intersection.symm ▸ ⟨hC.symm ▸ hxK, hPT hx⟩
  exact disjoint_def.mp hd hx (mem_sup_left (hR.symm ▸ hxR))

/-- Full source placement for a complement already conjugated into C_T(E).
The quotient map is proved injective, the mark z is proved outer, and the
quaternion image is constructed rather than supplied. -/
theorem complement_placement (h : IntersectionSetup T z L g R)
    (hsmall : OrderTwoOutsideDeltaZero L) (hempty : ¬ (deltaZero L).Nonempty)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hTC : commutingSylow T L = zpowers z)
    (htransport : (T : Subgroup G) ⊓ normalizer
      ((centralizer (L : Set G)).conjBy g : Set G) ≤ (T : Subgroup G).conjBy g)
    {P : Subgroup G}
    (hP : P ≤ (T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G))
    (hd : Disjoint P (fourGroup r z)) (he : Nonempty (P ≃* QuaternionGroup 2))
    (hplace : QuaternionPlacement (L.conjBy g)) :
    P ≤ (T : Subgroup G).conjBy g ⊓
      ((centralizer (L.conjBy g : Set G) ⊔ L.conjBy g) ⊔ fourGroup r z) ∧
    (T : Subgroup G).conjBy g ⊓
      ((centralizer (L.conjBy g : Set G) ⊔ L.conjBy g) ⊔ fourGroup r z) ≤
      L.conjBy g ⊔ fourGroup r z := by
  have hN : P ≤ normalizer (L.conjBy g : Set G) :=
    (hP.trans inf_le_right).trans (four_centralizer_le_r.trans
      (actor_centralizer_le_conjugate_normalizer h hr hr2))
  have hzN : z ∈ normalizer (L.conjBy g : Set G) :=
    fourGroup_le_conjugate_normalizer h hr hr2 (mem_sup_right (mem_zpowers z))
  have hdK := placed_complement_disjoint_kernel h (r_powers h hsmall hempty hr hr2)
    (hP.trans inf_le_left) hd
  have hlift := lift_quaternion_placement hN hzN h.involution
    (z_outside_conjugate_product h hsmall hempty hr hr2 hout) hdK he
    ((hP.trans inf_le_right).trans four_centralizer_le_z) hplace
  have hPTg : P ≤ (T : Subgroup G).conjBy g := by
    apply le_trans (le_inf (hP.trans inf_le_left) ?_) htransport
    rw [show (centralizer (L : Set G)).conjBy g = centralizer (L.conjBy g : Set G) from
      map_centralizer_equiv _ (MulAut.conj g), normalizers_eq_conjBy h.normalizers_eq g]
    exact hN
  exact ⟨le_inf hPTg (hlift.trans (sup_le_sup_left le_sup_right _)),
    conjugate_sylow_product_le h hTC htransport hr hr2⟩

/-- The complete conditional O₂(L)=1 graph-field contradiction on the prepared
source setup. NormalizerData, CenterlessComplementData and QuaternionPlacement
are precisely the intrinsic inputs owned by the model calculation. Saturation
and transport are the outputs of the source-choice constructors, not new fusion
restrictions. The actual complement, its nontrivial Frattini involution and its
L-conjugating witness are transported together. -/
theorem deltaZero_nonempty_prepared (h : IntersectionSetup T z L g R)
    (hsmall : OrderTwoOutsideDeltaZero L)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hout : r ∉ centralizer (L : Set G) ⊔ L)
    (hTC : commutingSylow T L = zpowers z)
    (hsat : SylowIn ((T : Subgroup G) ⊓ normalizer (R : Set G))
      (normalizer (L : Set G) ⊓ normalizer (R : Set G)))
    (htransport : (T : Subgroup G) ⊓ normalizer
      ((centralizer (L : Set G)).conjBy g : Set G) ≤ (T : Subgroup G).conjBy g)
    (d : NormalizerData L r z) (c : CenterlessComplementData d)
    (hplace : QuaternionPlacement (L.conjBy g)) : (deltaZero L).Nonempty := by
  by_contra hempty
  have hR := r_powers h hsmall hempty hr hr2
  have hs := four_centralizer_sylow h hR hr2 hsat
  obtain ⟨a, _ha, hQa, hPQa, hdis, _hsup, he, hp, v, hv, hv2, _hvL, l, hl, hprod⟩ :=
    exists_complement_in_sylow_centralizer h d c hs
  have hPa := hPQa.trans hQa
  have hplacement := complement_placement h hsmall hempty hr hr2 hout hTC htransport
    hPa hdis he hplace
  have hv1 : v ≠ 1 := by intro hv1; simp [hv1] at hv2
  exact hempty (deltaZero_nonempty_of_frattini_product h hsmall hr hr2 hout hp
    (hplacement.1.trans hplacement.2) ((hPa.trans inf_le_right).trans four_centralizer_le_r)
    hv hv1 hl hprod)

end CFSG.Quasithin.Chapter16.Intersections.GraphField.Centerless
