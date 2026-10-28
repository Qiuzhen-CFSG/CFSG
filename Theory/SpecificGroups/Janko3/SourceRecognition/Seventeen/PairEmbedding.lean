module
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.MarkedAction

/-!
# Rigidity of the pair stabilizer over the common overlap

In Baumeister's seventeen-point action, every order-fifteen element of the
literal H₁ ∩ H₂ cycles the fifteen points outside the distinguished pair.
The proof identifies the other sixteen points with the orbit of O₂(H₁)
and applies its faithful order-fifteen automorphism action.

In any competing S₃ × D₁₀ pair subgroup with the same overlap, an outside
involution acts by the eleventh power on that element. The quotient of two
such involutions fixes the distinguished points and centralizes the
fifteen-cycle, hence is a power of that cycle. This forces equality of the
pair subgroups. `SourceData.pair_image_unique` applies the argument to the
actual faithful coset action, without an orbit or uniqueness premise.

This proves the final comparison in Lemma 2.9 after the point and overlap
embeddings have been aligned. Their simultaneous alignment and the marked
PSL₂(16):2 identification remain separate steps of the source argument.

Source: Baumeister, *A geometry for groups of J₃-type* (2007),
Lemma 2.9, printed p.498.
-/

public noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Janko3.SourceRecognition.Seventeen

private theorem centralizer_of_two_fixed_points {X : Type*}
    (r t : Equiv.Perm X) (p q : X)
    (hrp : r p = p) (hrq : r q = q)
    (htrans : ∀ x y : X, x ≠ p → x ≠ q → y ≠ p → y ≠ q →
      ∃ n : ℤ, (r ^ n) x = y)
    (hne : ∃ x : X, x ≠ p ∧ x ≠ q)
    (htp : t p = p) (htq : t q = q) (hcomm : Commute t r) :
    t ∈ zpowers r := by
  obtain ⟨x, hxp, hxq⟩ := hne
  have htp' : t x ≠ p := fun h => hxp (t.injective (h.trans htp.symm))
  have htq' : t x ≠ q := fun h => hxq (t.injective (h.trans htq.symm))
  obtain ⟨n, hn⟩ := htrans x (t x) hxp hxq htp' htq'
  refine ⟨n, Equiv.ext fun y => ?_⟩
  by_cases hyp : y = p
  · subst y
    rw [htp]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hrp n
  by_cases hyq : y = q
  · subst y
    rw [htq]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hrq n
  obtain ⟨m, rfl⟩ := htrans x y hxp hxq hyp hyq
  calc
    (r ^ n) ((r ^ m) x) = (r ^ m) ((r ^ n) x) := by
      exact congrArg (fun f : Equiv.Perm X => f x) (Commute.zpow_zpow_self r n m).eq
    _ = (r ^ m) (t x) := by rw [hn]
    _ = t ((r ^ m) x) := (congrArg (fun f : Equiv.Perm X => f x)
      (hcomm.zpow_right m).eq).symm

private theorem complement_fifth_central (r : Complement) (hr : r ^ 15 = 1) :
    ∀ c : Complement, c * r ^ 5 = r ^ 5 * c := by
  revert r
  decide +kernel

private theorem pair_has_swap (r : PairGroup) (hr : r ^ 15 = 1) :
    ∃ a : PairGroup, a * a = 1 ∧ a * r * a⁻¹ = r ^ 11 := by
  have ht : ∀ r : PairGroup, r ^ 15 = 1 →
      ∃ i : Fin 3, let a : PairGroup := (Equiv.swap i (r.1 i), 1)
        a * a = 1 ∧ a * r * a⁻¹ = r ^ 11 := by decide +kernel
  obtain ⟨i, hi⟩ := ht r hr
  exact ⟨(Equiv.swap i (r.1 i), 1), hi⟩

private theorem exists_outside_swap {G : Type*} [Group G]
    (C P : Subgroup G) (hCP : C ≤ P)
    (eC : C ≃* Complement) (eP : P ≃* PairGroup)
    (r : C) (hr : orderOf r = 15) :
    ∃ a : G, a ∈ P ∧ a ∉ C ∧ a * a = 1 ∧ a * (r : G) * a⁻¹ = (r : G) ^ 11 := by
  let rP : P := ⟨r, hCP r.property⟩
  have hrpow : r ^ 15 = 1 := by simpa only [hr] using pow_orderOf_eq_one r
  have hp : (eP rP) ^ 15 = 1 := by
    rw [← map_pow]
    have hh : rP ^ 15 = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : C => (z : G)) hrpow
    rw [hh, map_one]
  obtain ⟨a, ha, har⟩ := pair_has_swap (eP rP) hp
  let b : P := eP.symm a
  have hb : b * b = 1 := by
    apply eP.injective
    simpa only [b, map_mul, map_one, MulEquiv.apply_symm_apply] using ha
  have hbr : b * rP * b⁻¹ = rP ^ 11 := by
    apply eP.injective
    simpa only [b, map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply] using har
  refine ⟨b, b.property, ?_, congrArg Subtype.val hb, congrArg Subtype.val hbr⟩
  intro hbC
  have hc : (b : G) * (r : G) ^ 5 = (r : G) ^ 5 * b := by
    have hh := complement_fifth_central (eC r) (by
      rw [← map_pow, hrpow, map_one]) (eC ⟨b, hbC⟩)
    have hh' : (⟨b, hbC⟩ : C) * r ^ 5 = r ^ 5 * ⟨b, hbC⟩ := by
      apply eC.injective
      simpa only [map_mul, map_pow] using hh
    exact congrArg Subtype.val hh'
  have hbrG : (b : G) * (r : G) * (b : G)⁻¹ = (r : G) ^ 11 := congrArg Subtype.val hbr
  have hh : (r : G) ^ 55 = (r : G) ^ 5 := by
    calc
      (r : G) ^ 55 = ((r : G) ^ 11) ^ 5 := pow_mul (r : G) 11 5
      _ = ((b : G) * (r : G) * (b : G)⁻¹) ^ 5 := by rw [hbrG]
      _ = (b : G) * (r : G) ^ 5 * (b : G)⁻¹ := conj_pow
      _ = (r : G) ^ 5 := by rw [hc, mul_inv_cancel_right]
  have hm := (pow_inj_mod).mp hh
  have ho : orderOf (r : G) = 15 := (Subgroup.orderOf_coe r).trans hr
  norm_num [ho] at hm

private theorem swaps_of_mem_pair {X : Type*} (p q : X)
    (a : Equiv.Perm X) (ha : a ∈ stabilizer (Equiv.Perm X) ({p, q} : Set X))
    (hp : a p ≠ p) : a p = q ∧ a q = p := by
  change a • ({p, q} : Set X) = {p, q} at ha
  rw [Set.smul_set_insert, Set.smul_set_singleton, Set.pair_eq_pair_iff] at ha
  exact ha.resolve_left (fun h => hp h.1)

private theorem pair_generation {X : Type*} (p q : X)
    (C P : Subgroup (Equiv.Perm X))
    (hC : P ⊓ stabilizer (Equiv.Perm X) p = C)
    (hP : P ≤ stabilizer (Equiv.Perm X) ({p, q} : Set X))
    (a : Equiv.Perm X) (haP : a ∈ P) (hap : a p = q) :
    C ⊔ zpowers a = P := by
  apply le_antisymm
  · exact sup_le (hC ▸ inf_le_left) (zpowers_le.mpr haP)
  · intro g hg
    have hgm : g ∈ C ⊔ zpowers a := by
      by_cases hgp : g p = p
      · exact (show C ≤ C ⊔ zpowers a from le_sup_left) (hC ▸ (show g ∈ P ⊓ stabilizer (Equiv.Perm X) p from ⟨hg, hgp⟩))
      · have hgq := (swaps_of_mem_pair p q g (hP hg) hgp).1
        have hm : a⁻¹ * g ∈ C := by
          rw [← hC]
          exact ⟨P.mul_mem (P.inv_mem haP) hg, by
            change a.symm (g p) = p
            rw [hgq, ← hap, a.symm_apply_apply]⟩
        have hh := (C ⊔ zpowers a).mul_mem
          ((show zpowers a ≤ C ⊔ zpowers a from le_sup_right) (mem_zpowers a))
          ((show C ≤ C ⊔ zpowers a from le_sup_left) hm)
        simpa only [mul_inv_cancel_left] using hh
    exact hgm

/-- Once the common overlap is fixed in the seventeen-point action, the pair
subgroup is forced. The order-fifteen orbit is the one constructed from the
point two-core, rather than an assumed conjugacy between the pair groups. -/
theorem pair_unique_of_common_overlap {X : Type*}
    (p q : X) (C P Q : Subgroup (Equiv.Perm X))
    (eC : C ≃* Complement) (eP : P ≃* PairGroup) (eQ : Q ≃* PairGroup)
    (hPC : P ⊓ stabilizer (Equiv.Perm X) p = C)
    (hQC : Q ⊓ stabilizer (Equiv.Perm X) p = C)
    (hP : P ≤ stabilizer (Equiv.Perm X) ({p, q} : Set X))
    (hQ : Q ≤ stabilizer (Equiv.Perm X) ({p, q} : Set X))
    (r : C) (hr : orderOf r = 15)
    (hrp : (r : Equiv.Perm X) p = p) (hrq : (r : Equiv.Perm X) q = q)
    (htrans : ∀ x y : X, x ≠ p → x ≠ q → y ≠ p → y ≠ q →
      ∃ n : ℤ, ((r : Equiv.Perm X) ^ n) x = y)
    (hne : ∃ x : X, x ≠ p ∧ x ≠ q) : P = Q := by
  have hCP : C ≤ P := hPC ▸ inf_le_left
  have hCQ : C ≤ Q := hQC ▸ inf_le_left
  obtain ⟨a, haP, haC, _ha2, har⟩ := exists_outside_swap C P hCP eC eP r hr
  obtain ⟨b, hbQ, hbC, _hb2, hbr⟩ := exists_outside_swap C Q hCQ eC eQ r hr
  have ha := swaps_of_mem_pair p q a (hP haP) (fun h =>
    haC (hPC ▸ (show a ∈ P ⊓ stabilizer (Equiv.Perm X) p from ⟨haP, h⟩)))
  have hb := swaps_of_mem_pair p q b (hQ hbQ) (fun h =>
    hbC (hQC ▸ (show b ∈ Q ⊓ stabilizer (Equiv.Perm X) p from ⟨hbQ, h⟩)))
  have hcomm : Commute (b⁻¹ * a) (r : Equiv.Perm X) := by
    change b⁻¹ * a * r = r * (b⁻¹ * a)
    have hh : a * r * a⁻¹ = b * r * b⁻¹ := har.trans hbr.symm
    calc
      b⁻¹ * a * r = b⁻¹ * (a * r * a⁻¹) * a := by group
      _ = b⁻¹ * (b * r * b⁻¹) * a := by rw [hh]
      _ = r * (b⁻¹ * a) := by group
  have hm : b⁻¹ * a ∈ zpowers (r : Equiv.Perm X) :=
    centralizer_of_two_fixed_points r (b⁻¹ * a) p q hrp hrq htrans hne
      (by change b.symm (a p) = p; rw [ha.1, ← hb.1, b.symm_apply_apply])
      (by change b.symm (a q) = q; rw [ha.2, ← hb.2, b.symm_apply_apply]) hcomm
  have haQ : a ∈ Q := by
    have hh := Q.mul_mem hbQ (hCQ ((zpowers_le.mpr r.property) hm))
    simpa only [mul_inv_cancel_left] using hh
  have hPQ : P ≤ Q := by
    rw [← pair_generation p q C P hPC hP a haP ha.1]
    exact sup_le hCQ (zpowers_le.mpr haQ)
  let : Finite Q := Finite.of_equiv PairGroup eQ.symm.toEquiv
  exact eq_of_le_of_card_ge hPQ (by
    rw [Nat.card_congr eP.toEquiv, Nat.card_congr eQ.toEquiv])

end Sporadic.Janko3.SourceRecognition.Seventeen

open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Janko3.SourceRecognition.Seventeen.SourceData
variable {G : Type*} [Group G] (S : SourceData G)

theorem core_orbit_of_complete
    (b : G) (hb : b * b = 1) (hout : b ∉ S.H1) (hb2 : b ∈ S.H2)
    (hc : CosetGraph.graph (S.cosetData b hb hout) = ⊤)
    (x : CosetGraph.Vertex (S.cosetData b hb hout))
    (hx : x ≠ CosetGraph.base (S.cosetData b hb hout)) :
    ∃ v : pCore 2 S.H1, ((v : S.H1) : G) •
      CosetGraph.other (S.cosetData b hb hout) = x := by
  let D := S.cosetData b hb hout
  have horbit : x ∈ orbit S.H1 (CosetGraph.other D) := by
    have hx' : (CosetGraph.graph D).Adj (CosetGraph.base D) x := by
      rw [hc]
      exact hx.symm
    rwa [CosetGraph.graph, SwappedOrbital.adj_base, CosetGraph.point_stabilizer] at hx'
  obtain ⟨g, hg⟩ := horbit
  obtain ⟨⟨v, c⟩, hvc, _⟩ := S.overlap_complements_core.existsUnique g
  have hfix : (c : S.H1) • CosetGraph.other D = CosetGraph.other D := by
    have hh : c.val ∈ CosetGraph.edgeStabilizer D :=
      (S.edge_stabilizer b hb hout hb2).symm ▸ c.property
    exact hh
  refine ⟨v, ?_⟩
  change (v : S.H1) • CosetGraph.other D = x
  rw [← hg, ← hvc]
  change (v : S.H1) • CosetGraph.other D = ((v : S.H1) * c) • CosetGraph.other D
  rw [mul_smul, hfix]

/-- The order-fifteen element of the literal overlap cycles all points except
for the two distinguished cosets. This supplies the orbit used in Lemma 2.9. -/
theorem overlap_fifteen_transitive
    (b : G) (hb : b * b = 1) (hout : b ∉ S.H1) (hb2 : b ∈ S.H2) (hb3 : b ∈ S.H3)
    (r : (S.H1 ⊓ S.H2 : Subgroup G)) (hr : orderOf r = 15)
    (x y : CosetGraph.Vertex (S.cosetData b hb hout))
    (hxp : x ≠ CosetGraph.base (S.cosetData b hb hout))
    (hxq : x ≠ CosetGraph.other (S.cosetData b hb hout))
    (hyp : y ≠ CosetGraph.base (S.cosetData b hb hout))
    (hyq : y ≠ CosetGraph.other (S.cosetData b hb hout)) :
    ∃ n : ℤ, (r : G) ^ n • x = y := by
  let D := S.cosetData b hb hout
  have hc := (S.consequences b hb hout hb2 hb3).2.2.1
  obtain ⟨v, hv⟩ := core_orbit_of_complete S b hb hout hb2 hc x hxp
  obtain ⟨w, hw⟩ := core_orbit_of_complete S b hb hout hb2 hc y hyp
  have hv1 : v ≠ 1 := by
    intro he
    apply hxq
    rw [← hv, he]
    exact one_smul G _
  have hw1 : w ≠ 1 := by
    intro he
    apply hyq
    rw [← hw, he]
    exact one_smul G _
  let rH : S.H2.subgroupOf S.H1 := ⟨⟨r, r.property.1⟩, r.property.2⟩
  have hrH : orderOf rH = 15 := by
    calc
      orderOf rH = orderOf (rH : S.H1) := (Subgroup.orderOf_coe rH).symm
      _ = orderOf ((rH : S.H1) : G) := (Subgroup.orderOf_coe (rH : S.H1)).symm
      _ = 15 := (Subgroup.orderOf_coe r).trans hr
  have ho : orderOf (S.overlapAction rH) = 15 :=
    (orderOf_injective S.overlapAction S.overlapAction_injective rH).trans hrH
  let : Finite (pCore 2 S.H1) := Nat.finite_of_card_ne_zero (by rw [S.core_card]; decide)
  obtain ⟨n, hn⟩ := MulAut.exists_zpow_apply_eq_of_order_fifteen S.core_card
    (S.overlapAction rH) ho v w hv1 hw1
  rw [← map_zpow] at hn
  have he := congrArg (fun z : pCore 2 S.H1 => ((z : S.H1) : G)) hn
  change (r : G)^n * ((v : S.H1) : G) * ((r : G)^n)⁻¹ = ((w : S.H1) : G) at he
  have hfix : (r : G) • CosetGraph.other D = CosetGraph.other D := by
    have hh : rH.val ∈ CosetGraph.edgeStabilizer D :=
      (S.edge_stabilizer b hb hout hb2).symm ▸ rH.property
    exact hh
  have hfixn : (r : G)^n • CosetGraph.other D = CosetGraph.other D :=
    smul_eq_self_of_mem_zpowers (mem_zpowers_iff.mpr ⟨n, rfl⟩) hfix
  refine ⟨n, ?_⟩
  rw [← hv, ← hw, ← mul_smul]
  have hm : (r : G)^n * ((v : S.H1) : G) = ((w : S.H1) : G) * (r : G)^n := by
    rw [← he]
    group
  rw [hm, mul_smul, hfixn]


/-- Uniqueness of the pair subgroup over its actual common overlap in the
faithful action constructed in Lemma 2.7. Only the alignment of that overlap
remains as input; the orbit and the outside-involution comparison are proved. -/
theorem pair_image_unique
    (b : G) (hb : b * b = 1) (hout : b ∉ S.H1) (hb2 : b ∈ S.H2) (hb3 : b ∈ S.H3)
    (Q : Subgroup (Equiv.Perm (CosetGraph.Vertex (S.cosetData b hb hout))))
    (eQ : Q ≃* PairGroup)
    (hQ : Q ≤ stabilizer (Equiv.Perm (CosetGraph.Vertex (S.cosetData b hb hout)))
      ({CosetGraph.base (S.cosetData b hb hout),
        CosetGraph.other (S.cosetData b hb hout)} : Set _))
    (hQC : Q ⊓ stabilizer (Equiv.Perm (CosetGraph.Vertex (S.cosetData b hb hout)))
      (CosetGraph.base (S.cosetData b hb hout)) =
      (S.H1 ⊓ S.H2).map (toPermHom G (CosetGraph.Vertex (S.cosetData b hb hout)))) :
    S.H2.map (toPermHom G (CosetGraph.Vertex (S.cosetData b hb hout))) = Q := by
  classical
  let D := S.cosetData b hb hout
  let X := CosetGraph.Vertex D
  let ρ := toPermHom G X
  let P := S.H2.map ρ
  let C := (S.H1 ⊓ S.H2).map ρ
  obtain ⟨hf, _, _, _, hcard, _, _⟩ := S.consequences b hb hout hb2 hb3
  let : FaithfulSMul G X := hf
  have hρ : Function.Injective ρ := MulAction.toPerm_injective
  let eC0 := equivMapOfInjective (S.H1 ⊓ S.H2) ρ hρ
  let eC : C ≃* Complement := eC0.symm.trans S.overlap12
  let eP : P ≃* PairGroup := (equivMapOfInjective S.H2 ρ hρ).symm.trans S.pairEquiv
  have hPC : P ⊓ stabilizer (Equiv.Perm X) (CosetGraph.base D) = C := by
    ext t
    constructor
    · rintro ⟨⟨g, hg, rfl⟩, hp⟩
      have hg1 : g ∈ S.H1 := by
        change g ∈ D.point
        rw [← CosetGraph.point_stabilizer D]
        exact hp
      exact ⟨g, ⟨hg1, hg⟩, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, hg.2, rfl⟩, ?_⟩
      have hh : g ∈ stabilizer G (CosetGraph.base D) :=
        (CosetGraph.point_stabilizer D).symm ▸ hg.1
      exact hh
  have hP : P ≤ stabilizer (Equiv.Perm X)
      ({CosetGraph.base D, CosetGraph.other D} : Set X) := by
    rintro t ⟨g, hg, rfl⟩
    have hh : g ∈ stabilizer G ({CosetGraph.base D, CosetGraph.other D} : Set X) :=
      (S.setwise_pair_stabilizer b hb hout hb2).symm ▸ hg
    exact hh
  let r0 := S.overlap12.symm (Multiplicative.ofAdd (1 : ZMod 3), DihedralGroup.r 1)
  have hr0 : orderOf r0 = 15 := by
    rw [← orderOf_injective S.overlap12.toMonoidHom S.overlap12.injective r0]
    change orderOf (S.overlap12 (S.overlap12.symm _)) = 15
    rw [MulEquiv.apply_symm_apply, Prod.orderOf_mk,
      orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one, DihedralGroup.orderOf_r_one]
    decide
  let r : C := eC0 r0
  have hr : orderOf r = 15 :=
    (orderOf_injective eC0.toMonoidHom eC0.injective r0).trans hr0
  have hrcoe : (r : Equiv.Perm X) = ρ r0 := coe_equivMapOfInjective_apply _ _ _ _
  have hrfix : (r0 : G) ∈ stabilizer G (CosetGraph.base D) ⊓
      stabilizer G (CosetGraph.other D) := by
    rw [S.pointwise_pair_stabilizer b hb hout hb2]
    exact r0.property
  have hrp : (r : Equiv.Perm X) (CosetGraph.base D) = CosetGraph.base D := by
    rw [hrcoe]
    exact hrfix.1
  have hrq : (r : Equiv.Perm X) (CosetGraph.other D) = CosetGraph.other D := by
    rw [hrcoe]
    exact hrfix.2
  have htrans : ∀ x y : X, x ≠ CosetGraph.base D → x ≠ CosetGraph.other D →
      y ≠ CosetGraph.base D → y ≠ CosetGraph.other D →
      ∃ n : ℤ, ((r : Equiv.Perm X)^n) x = y := by
    intro x y hxp hxq hyp hyq
    obtain ⟨n, hn⟩ := S.overlap_fifteen_transitive b hb hout hb2 hb3 r0 hr0
      x y hxp hxq hyp hyq
    refine ⟨n, ?_⟩
    rw [hrcoe, ← map_zpow]
    exact hn
  have hne : ∃ x : X, x ≠ CosetGraph.base D ∧ x ≠ CosetGraph.other D := by
    let : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
    let : Fintype X := Fintype.ofFinite X
    by_contra! hh
    have hsub : (Finset.univ : Finset X) ⊆ {CosetGraph.base D, CosetGraph.other D} := by
      intro x _
      by_cases hx : x = CosetGraph.base D
      · simp only [Finset.mem_insert, Finset.mem_singleton, hx, true_or]
      · simp only [Finset.mem_insert, Finset.mem_singleton, hh x hx, or_true]
    have hc' : (Finset.univ : Finset X).card ≤ 2 :=
      (Finset.card_le_card hsub).trans Finset.card_le_two
    have hc : Fintype.card X ≤ 2 := by simpa only [Finset.card_univ] using hc'
    rw [← Nat.card_eq_fintype_card, hcard] at hc
    omega
  exact pair_unique_of_common_overlap (CosetGraph.base D) (CosetGraph.other D)
    C P Q eC eP eQ hPC hQC hP hQ r hr hrp hrq htrans hne

end Sporadic.Janko3.SourceRecognition.Seventeen.SourceData
