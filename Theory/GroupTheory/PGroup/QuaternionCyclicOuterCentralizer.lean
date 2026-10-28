module

public import Theory.GroupTheory.PGroup.CyclicTwoDisplacement
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Outer involutions on quaternion–cyclic central products

Let `R = Q C`, where `Q` is quaternion of order eight, `C` is cyclic,
the factors commute, and their intersection has order two. If an ambient
involution induces an outer automorphism on `Q` and inverts an element of
order four in the cyclic two-group `C`, its centralizer in `R` has order four.

A kernel-checked table of quaternion generator images counts four quaternion
elements whose displacement is central. The intersection `Q ∩ C` is exactly
the center of `Q`. Its elements square to one, so each inverse displacement
is a square in `C`; the cyclic displacement theorem supplies exactly two
corrections. Thus eight pairs in `Q × C` have fixed product. The multiplication
map has kernel of order two, leaving four fixed elements in `R`.

The generator-image encoding follows `QuaternionEightAut.lean`. The group
calculation is from Janko–Thompson (1970), §4, Case 2, printed p.393:
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
No elementary-rank, uniqueness, or recognition hypothesis is used.
-/

namespace QuaternionGroup
private abbrev Q8 := QuaternionGroup 2
-- Generator-image encoding, as in QuaternionEightAut.
private def imageMap (p : Q8 × Q8) : Q8 → Q8
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val
private theorem imageMap_aut (e : MulAut Q8) (x : Q8) :
    imageMap (e (a 1), e (xa 0)) x = e x := by
  cases x with
  | a i =>
    change (e (a 1)) ^ i.val = e (a i)
    rw [← map_pow, a_one_pow, ZMod.natCast_zmod_val]
  | xa i =>
    change e (xa 0) * (e (a 1)) ^ i.val = e (xa i)
    rw [← map_pow, ← map_mul, a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxSize 100000 in
private theorem outer_table : ∀ p : Q8 × Q8,
    p.1 ^ 2 = a 2 → p.2 ^ 2 = a 2 → p.1 * p.2 ≠ p.2 * p.1 →
    (∀ x, imageMap p (imageMap p x) = x) →
    (¬ ∃ q, ∀ x, imageMap p x = q * x * q⁻¹) →
    Fintype.card {x : Q8 // ∀ y : Q8,
      y * (x⁻¹ * imageMap p x) = (x⁻¹ * imageMap p x) * y} = 4 := by
  decide

private theorem model_outer_card (e : MulAut Q8)
    (he : ∀ x, e (e x) = x) (hout : ¬ ∃ q, ∀ x, e x = q * x * q⁻¹) :
    Nat.card {x : Q8 // x⁻¹ * e x ∈ Subgroup.center Q8} = 4 := by
  have hs (x : Q8) (hx : x ^ 2 ≠ 1) : x ^ 2 = a 2 := by
    exact (by decide : ∀ y : Q8, y ^ 2 ≠ 1 → y ^ 2 = a 2) x hx
  have h1 : (e (a 1)) ^ 2 = a 2 := hs _ (by
    intro h
    have := e.injective (by simpa only [map_pow, map_one] using h : e ((a 1)^2) = e 1)
    exact (by decide : (a 1 : Q8)^2 ≠ 1) this)
  have h2 : (e (xa 0)) ^ 2 = a 2 := hs _ (by
    intro h
    have := e.injective (by simpa only [map_pow, map_one] using h : e ((xa 0)^2) = e 1)
    exact (by decide : (xa 0 : Q8)^2 ≠ 1) this)
  have hn : e (a 1) * e (xa 0) ≠ e (xa 0) * e (a 1) := by
    intro h
    have := e.injective (show e (a 1 * xa 0) = e (xa 0 * a 1) by simpa only [map_mul] using h)
    exact (by decide : (a 1 : Q8) * xa 0 ≠ xa 0 * a 1) this
  have ht := outer_table (e (a 1), e (xa 0)) h1 h2 hn
    (by simpa only [imageMap_aut] using he) (by simpa only [imageMap_aut] using hout)
  simpa only [imageMap_aut, ← Subgroup.mem_center_iff, Nat.card_eq_fintype_card] using ht

private theorem outer_central_displacement_card {G : Type*} [Group G]
    (model : G ≃* QuaternionGroup 2) (e : MulAut G)
    (he : ∀ x, e (e x) = x) (hout : ¬ ∃ q, ∀ x, e x = q * x * q⁻¹) :
    Nat.card {x : G // x⁻¹ * e x ∈ Subgroup.center G} = 4 := by
  let a := MulAut.congr model e
  have ha (x : G) : a (model x) = model (e x) := by simp [a, MulAut.congr_apply]
  have hcenter (x : G) : model x ∈ Subgroup.center (QuaternionGroup 2) ↔
      x ∈ Subgroup.center G := by
    simp only [Subgroup.mem_center_iff]
    constructor
    · intro h y
      apply model.injective
      simpa only [map_mul] using h (model y)
    · intro h y
      obtain ⟨z, rfl⟩ := model.surjective y
      simpa only [map_mul] using congrArg model (h z)
  have hcount := model_outer_card a (by
    intro x
    obtain ⟨y, rfl⟩ := model.surjective x
    rw [ha, ha, he]) (by
    rintro ⟨q, hq⟩
    apply hout
    refine ⟨model.symm q, fun x => model.injective ?_⟩
    simpa only [map_mul, map_inv, model.apply_symm_apply, ha] using hq (model x))
  have e' : {x : G // x⁻¹ * e x ∈ Subgroup.center G} ≃
      {x : QuaternionGroup 2 // x⁻¹ * a x ∈ Subgroup.center (QuaternionGroup 2)} :=
    model.toEquiv.subtypeEquiv (fun x => by
      change _ ↔ (model x)⁻¹ * a (model x) ∈ _
      rw [ha, ← map_inv, ← map_mul, hcenter])
  exact (Nat.card_congr e').trans hcount

private theorem center_card_of_equiv {G : Type*} [Group G]
    (model : G ≃* QuaternionGroup 2) : Nat.card (Subgroup.center G) = 2 := by
  have h (x : G) : x ∈ Subgroup.center G ↔
      model x ∈ Subgroup.center (QuaternionGroup 2) := by
    simp only [Subgroup.mem_center_iff]
    constructor
    · intro h y
      obtain ⟨z, rfl⟩ := model.surjective y
      simpa only [map_mul] using congrArg model (h z)
    · intro h y
      apply model.injective
      simpa only [map_mul] using h (model y)
  rw [Nat.card_congr (model.toEquiv.subtypeEquiv h), Nat.card_eq_fintype_card]
  decide
end QuaternionGroup

namespace Subgroup
private theorem card_fixed_product
    {P : Type*} [Group P] [Finite P] (R Q C : Subgroup P) [C.Normal]
    (hcomm : C ≤ centralizer (Q : Set P)) (hjoin : Q ⊔ C = R)
    (t : P) (hinter : Nat.card (Q ⊓ C : Subgroup P) = 2)
    (hcount : Nat.card {q : Q // (q : P)⁻¹ * (t * q * t⁻¹) ∈ C} = 4)
    (hcorrection : ∀ q : Q, (q : P)⁻¹ * (t * q * t⁻¹) ∈ C →
      Nat.card {c : C // t * ((q : P) * c) * t⁻¹ = (q : P) * c} = 2) :
    Nat.card (R ⊓ centralizer ({t} : Set P) : Subgroup P) = 4 := by
  classical
  let m : Q × C →* P :=
    { toFun := fun x => (x.1 : P) * x.2
      map_one' := by simp
      map_mul' := by
        rintro ⟨q,c⟩ ⟨q',c'⟩
        change ((q : P) * q') * ((c : P) * c') = ((q : P) * c) * ((q' : P) * c')
        have hc := mem_centralizer_iff.mp (hcomm c.property) q' q'.property
        calc
          _ = (q : P) * ((q' : P) * c) * c' := by group
          _ = (q : P) * ((c : P) * q') * c' := by rw [hc]
          _ = _ := by group }
  have hker : Nat.card m.ker = 2 := by
    let e : m.ker ≃ ↥(Q ⊓ C) :=
      { toFun := fun x => ⟨x.1.1, x.1.1.property, by
          have h : (x.1.1 : P) * x.1.2 = 1 := x.property
          rw [mul_eq_one_iff_eq_inv] at h
          rw [h]
          exact C.inv_mem x.1.2.property⟩
        invFun := fun z => ⟨(⟨z, z.property.1⟩, ⟨(z : P)⁻¹, C.inv_mem z.property.2⟩), by
          change (z : P) * (z : P)⁻¹ = 1
          exact mul_inv_cancel _⟩
        left_inv := by
          intro x
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            have h : (x.1.1 : P) * x.1.2 = 1 := x.property
            exact (eq_inv_of_mul_eq_one_right h).symm
        right_inv := by intro z; rfl }
    exact (Nat.card_congr e).trans hinter
  let K := R ⊓ centralizer ({t} : Set P)
  let F := {x : Q × C // t * m x * t⁻¹ = m x}
  have hfixed (x : Q × C) : t * m x * t⁻¹ = m x ↔ m x ∈ K := by
    have hr : m x ∈ R := hjoin ▸ mul_mem_sup x.1.property x.2.property
    change _ ↔ m x ∈ R ∧ m x ∈ centralizer ({t} : Set P)
    rw [and_iff_right hr, mem_centralizer_singleton_iff]
    exact ⟨fun h => (mul_inv_eq_iff_eq_mul.mp h).symm,
      fun h => mul_inv_eq_iff_eq_mul.mpr h.symm⟩
  have hlower : Nat.card F = Nat.card K * 2 := by
    let e : (Σ k : K, {x : Q × C // m x = k}) ≃ F :=
      Equiv.sigmaSubtypeFiberEquivSubtype m hfixed
    let : Fintype K := Fintype.ofFinite K
    rw [← Nat.card_congr e, Nat.card_sigma]
    have hf (k : K) : Nat.card {x : Q × C // m x = k} = 2 := by
      have hk : (k : P) ∈ Q ⊔ C := hjoin ▸ k.property.1
      obtain ⟨q, hq, c, hc, he⟩ := mem_sup_of_normal_right.mp hk
      let x : Q × C := (⟨q,hq⟩,⟨c,hc⟩)
      have hx : m x = k := he
      rw [← hx]
      exact (Nat.card_congr (m.fiberEquivKer x)).trans hker
    simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card]
  let T := {q : Q // (q : P)⁻¹ * (t * q * t⁻¹) ∈ C}
  have hmem (q : Q) (c : C)
      (h : t * ((q : P) * c) * t⁻¹ = (q : P) * c) :
      (q : P)⁻¹ * (t * q * t⁻¹) ∈ C := by
    have he : (q : P)⁻¹ * (t * q * t⁻¹) =
        (c : P) * (t * c * t⁻¹)⁻¹ := by
      apply (mul_right_cancel_iff (a := t * (c : P) * t⁻¹)).mp
      calc
        _ = (q : P)⁻¹ * (t * ((q : P) * c) * t⁻¹) := by group
        _ = (c : P) := by rw [h]; group
        _ = _ := by group
    rw [he]
    exact C.mul_mem c.property (C.inv_mem ((inferInstance : C.Normal).conj_mem _ c.property _))
  have hupper : Nat.card F = 4 * 2 := by
    let e : F ≃ (Σ q : T, {c : C // t * ((q.1 : P) * c) * t⁻¹ = (q.1 : P) * c}) :=
      { toFun := fun x => ⟨⟨x.1.1, hmem x.1.1 x.1.2 x.property⟩, ⟨x.1.2, x.property⟩⟩
        invFun := fun x => ⟨(x.1.1,x.2.1),x.2.property⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    let : Fintype T := Fintype.ofFinite T
    rw [Nat.card_congr e, Nat.card_sigma]
    have hc (q : T) := hcorrection q.1 q.property
    simp only [hc, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, ← Nat.card_eq_fintype_card]
    exact congrArg (· * 2) hcount
  change Nat.card K = 4
  omega
end Subgroup

namespace Subgroup
private theorem square_root_of_square_eq_one
    {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (d : G) (hd : orderOf d = 4) (u : G) (hu : u ^ 2 = 1) :
    ∃ y : G, u = y ^ 2 := by
  by_cases h : u = 1
  · exact ⟨1, by simpa using h⟩
  have ho : orderOf u = 2 := orderOf_eq_prime hu h
  have hd2 : orderOf (d ^ 2) = 2 := by rw [orderOf_pow, hd]; norm_num
  exact ⟨d, IsCyclic.eq_of_orderOf_eq_two ho hd2⟩

/-- An outer involution on a quaternion–cyclic central product has centralizer
of order four if it inverts a cyclic element of order four. -/
public theorem card_inf_centralizer_quaternion_cyclic_of_inverts_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (R Q C : Subgroup P) [Q.Normal] [C.Normal] [IsCyclic C]
    (hQ : Nonempty (Q ≃* QuaternionGroup 2))
    (hcomm : C ≤ centralizer (Q : Set P)) (hjoin : Q ⊔ C = R)
    (hinter : Nat.card (Q ⊓ C : Subgroup P) = 2)
    (t : P) (ht : t ^ 2 = 1)
    (houter : ¬ ∃ q₀ : Q, ∀ q : Q,
      t * (q : P) * t⁻¹ = (q₀ : P) * (q : P) * (q₀ : P)⁻¹)
    (d : C) (hd : orderOf d = 4) (htd : t * (d : P) * t⁻¹ = (d : P)⁻¹) :
    Nat.card (R ⊓ centralizer ({t} : Set P) : Subgroup P) = 4 := by
  classical
  obtain ⟨model⟩ := hQ
  let a : MulAut Q := MulAut.conjNormal t
  let b : MulAut C := MulAut.conjNormal t
  have hb (c : C) : (b c : P) = t * c * t⁻¹ := rfl
  have ha2 (q : Q) : a (a q) = q := by
    have hh : a ^ 2 = 1 := by
      change (MulAut.conjNormal t : MulAut Q) ^ 2 = 1
      rw [← map_pow, ht, map_one]
    exact DFunLike.congr_fun hh q
  have hao : ¬ ∃ q₀ : Q, ∀ q : Q, a q = q₀ * q * q₀⁻¹ := by
    rintro ⟨q₀,hq₀⟩
    exact houter ⟨q₀,fun q => congrArg Subtype.val (hq₀ q)⟩
  have hIcard : Nat.card (C.subgroupOf Q) = 2 := by
    let e : C.subgroupOf Q ≃ ↥(Q ⊓ C) :=
      { toFun := fun x => ⟨x.1,x.1.property,x.property⟩
        invFun := fun x => ⟨⟨x,x.property.1⟩,x.property.2⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    exact (Nat.card_congr e).trans hinter
  have hI : C.subgroupOf Q = center Q := by
    apply eq_of_le_of_card_ge
    · intro q hq
      apply mem_center_iff.mpr
      intro q'
      apply Subtype.ext
      exact mem_centralizer_iff.mp (hcomm hq) q' q'.property
    · rw [QuaternionGroup.center_card_of_equiv model, hIcard]
  have hcount : Nat.card {q : Q // (q : P)⁻¹ * (t * q * t⁻¹) ∈ C} = 4 := by
    have hh (q : Q) : (q : P)⁻¹ * (t * q * t⁻¹) ∈ C ↔
        q⁻¹ * a q ∈ center Q := by
      rw [← hI]
      rfl
    exact (Nat.card_congr (Equiv.subtypeEquivRight hh)).trans
      (QuaternionGroup.outer_central_displacement_card model a ha2 hao)
  apply card_fixed_product R Q C hcomm hjoin t hinter hcount
  intro q hq
  let δ : ↥(Q ⊓ C) := ⟨(q : P)⁻¹ * (t * q * t⁻¹),
    Q.mul_mem (Q.inv_mem q.property) (a q).property, hq⟩
  have hδ2 : δ ^ 2 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [← hinter]
    exact _root_.orderOf_dvd_natCard δ
  let u : C := ⟨(δ : P)⁻¹, C.inv_mem δ.property.2⟩
  have hu : u ^ 2 = 1 := by
    apply Subtype.ext
    have h := congrArg (fun x : ↥(Q ⊓ C) => (x : P)) hδ2
    change ((δ : P)⁻¹)^2 = 1
    rw [inv_pow, show (δ : P)^2 = 1 from h, inv_one]
  obtain ⟨y,hy⟩ := square_root_of_square_eq_one d hd u hu
  have he (c : C) : t * ((q : P) * c) * t⁻¹ = (q : P) * c ↔
      c⁻¹ * b c = y ^ 2 := by
    rw [← hy]
    have hc : (δ : P) * (c : P)⁻¹ = (c : P)⁻¹ * δ :=
      mem_centralizer_iff.mp (hcomm (C.inv_mem c.property)) δ δ.property.1
    have hc' : (c : P)⁻¹ * (δ : P) = (δ : P) * (c : P)⁻¹ := hc.symm
    have hcalc : ((q : P) * c)⁻¹ * (t * ((q : P) * c) * t⁻¹) =
        (δ : P) * ((c : P)⁻¹ * (b c : P)) := by
      calc
        _ = (c : P)⁻¹ * (δ : P) * (b c : P) := by dsimp [δ]; rw [hb]; group
        _ = _ := by rw [hc', mul_assoc]
    conv_lhs => rw [eq_comm, ← inv_mul_eq_one]
    rw [hcalc, mul_eq_one_iff_eq_inv']
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact (hP.to_subgroup C).card_displacement_fiber_of_inverts_order_four b d hd
    (Subtype.ext htd) y
end Subgroup
