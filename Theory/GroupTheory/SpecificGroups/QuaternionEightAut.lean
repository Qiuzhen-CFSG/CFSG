module
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic.NormNum

/-!
# Automorphisms and inner automorphisms of the quaternion group of order eight

The automorphism group of `QuaternionGroup 2` has order twenty-four, and its
inner automorphism subgroup has index six. These are the standard automorphism
counts used for quaternion subgroups in Alperin–Brauer–Gorenstein, Chapter II,
§1, Proposition 1, article pp. 10–11, in
`refs/latex/alperin-brauer-gorenstein.tex`.

An automorphism is determined by the images of the generators `a 1` and
`xa 0`. Those images are a noncommuting ordered pair, both squaring to the
central involution `a 2`. Conversely every such pair defines an automorphism
by the two quaternion normal forms. Kernel-checked finite calculations verify
the multiplication table for this map and count the twenty-four pairs.
The conjugation kernel consists of the two elements commuting with every
element. Thus the inner automorphism subgroup has order four, and the
index-cardinality formula gives index six.

The concrete encoding and finite tables are private. The inner-subgroup index
is also transported through actual quaternion isomorphisms. Two explicit
automorphisms realize the standard quaternion generators as differences
`x⁻¹ * e x`; these supply the full-action local focal calculation.
Finally, every element of order four occurs as the first component of a good
pair. Composing one corresponding automorphism with the inverse of another
proves transitivity on elements of order four, as needed for full-automizer
fusion in the same proposition. The same finite encoding shows that a
nonidentity automorphism whose cube is the identity fixes only central elements:
the twenty-four good pairs are tested for cubing to the identity and having a
moved element, and their fixed points commute with every quaternion element.
This intrinsic fixed-point calculation is used in Stellmacher (9.1), journal
p. 48, for the order-three action on a quaternion central product. A further
finite table identifies every automorphism acting trivially modulo the center
with conjugation by a quaternion element, supplying the innerness step for
that factor action. This innerness result is transported through an explicit
quaternion isomorphism to apply directly to subgroup factors. The order-three
calculation also holds for fixed cosets modulo the center: a central difference
`x⁻¹ * e x` forces `x` to be central. Its finite table and isomorphism transport
control centralizers on products of the quaternion factors. Finally, a finite
table shows that if an automorphism and its product with its conjugate under a
nonidentity cubic automorphism both have eighth power one, then the original
automorphism is inner. This is the concrete automorphism calculation used to
control two-subgroups normalized by a cubic action. A further finite table
selects an actual involution inverting a nontrivial cubic action whose class
modulo central differences is moved by the prescribed factor-swap action.
This supplies the invariant diagonal selection in the central product.
-/

namespace QuaternionGroup
private abbrev Q := QuaternionGroup 2
private def goodPair (p : Q × Q) : Prop :=
  p.1 ^ 2 = a 2 ∧ p.2 ^ 2 = a 2 ∧ p.1 * p.2 ≠ p.2 * p.1
private instance : DecidablePred goodPair := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private abbrev Pairs := {p : Q × Q // goodPair p}
private def pairMap (p : Q × Q) : Q → Q
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val
set_option maxRecDepth 10000 in
private theorem pair_map_spec : ∀ p : Pairs,
    Function.Bijective (pairMap p.val) ∧
    (∀ x y : Q, pairMap p.val (x*y)=pairMap p.val x * pairMap p.val y) ∧
    pairMap p.val (a 1)=p.val.1 ∧ pairMap p.val (xa 0)=p.val.2 := by
  decide
private noncomputable def pairAut (p : Pairs) : MulAut Q :=
  MulEquiv.ofBijective
    ({ toFun := pairMap p.val
       map_one' := by change p.val.1^0=1; exact pow_zero _
       map_mul' := (pair_map_spec p).2.1 } : Q →* Q)
    (pair_map_spec p).1
private theorem count_pairs : Nat.card Pairs=24 := by
  rw [Nat.card_eq_fintype_card]
  decide

private theorem square_of_square_ne_one : ∀ x : Q, x^2 ≠ 1 → x^2=a 2 := by decide
private def autPair (e : MulAut Q) : Pairs := by
  refine ⟨(e (a 1),e (xa 0)),?_,?_,?_⟩
  · apply square_of_square_ne_one
    intro h
    have hi : (a 1 : Q)^2 ≠ 1 := by decide
    apply hi
    apply e.injective
    simpa only [map_pow,map_one] using h
  · apply square_of_square_ne_one
    intro h
    have hi : (xa 0 : Q)^2 ≠ 1 := by decide
    apply hi
    apply e.injective
    simpa only [map_pow,map_one] using h
  · intro h
    have hi : (a 1 : Q)*xa 0 ≠ xa 0*a 1 := by decide
    apply hi
    apply e.injective
    simpa only [map_mul] using h
private noncomputable def autEquivPairs : MulAut Q ≃ Pairs where
  toFun := autPair
  invFun := pairAut
  left_inv e := by
    apply MulEquiv.ext
    intro x
    cases x with
    | a i =>
      change (e (a 1))^i.val=e (a i)
      rw [←map_pow,a_one_pow,ZMod.natCast_zmod_val]
    | xa i =>
      change e (xa 0)*(e (a 1))^i.val=e (xa i)
      rw [←map_pow,←map_mul,a_one_pow,ZMod.natCast_zmod_val,xa_mul_a,zero_add]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (pair_map_spec p).2.2.1
    · exact (pair_map_spec p).2.2.2
/-- The automorphism group of the quaternion group of order eight has order twenty-four. -/
public theorem card_mulAut_two : Nat.card (MulAut (QuaternionGroup 2))=24 :=
  (Nat.card_congr autEquivPairs).trans count_pairs
private theorem inner_ker_card :
    Nat.card (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).ker = 2 := by
  let P : QuaternionGroup 2 → Prop := fun x => ∀ y : QuaternionGroup 2, x * y = y * x
  have hP : ∀ x : QuaternionGroup 2,
      x ∈ (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).ker ↔ P x := by
    intro x
    constructor
    · intro hx y
      have he : MulAut.conj x = 1 := hx
      have hxy : x * y * x⁻¹ = y := congrArg (fun f : MulAut (QuaternionGroup 2) => f y) he
      exact (mul_inv_eq_iff_eq_mul).mp hxy
    · intro hx
      change MulAut.conj x = 1
      ext y
      change x * y * x⁻¹ = y
      rw [hx y, mul_inv_cancel_right]
  have hc : Fintype.card {x : QuaternionGroup 2 // P x} = 2 := by decide
  rw [Nat.card_congr (Equiv.subtypeEquivRight hP), Nat.card_eq_fintype_card, hc]

private theorem inner_range_card :
    Nat.card (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).range = 4 := by
  have h := (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).ker.card_mul_index
  rw [Subgroup.index_ker, inner_ker_card, Nat.card_eq_fintype_card (α := QuaternionGroup 2), QuaternionGroup.card] at h
  omega


/-- Inner automorphisms have index six in the automorphism group of `QuaternionGroup 2`. -/
public theorem index_range_conj_two :
    (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).range.index=6 := by
  have h := (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).range.index_mul_card
  rw [inner_range_card,card_mulAut_two] at h
  omega
/-- The inner automorphism index is six for every group isomorphic to `QuaternionGroup 2`. -/
public theorem index_range_conj_of_equiv {G : Type*} [Group G] (e : G ≃* QuaternionGroup 2) :
    (MulAut.conj : G →* MulAut G).range.index=6 := by
  have he : (MulAut.conj : G →* MulAut G).range.map (MulAut.congr e).toMonoidHom =
      (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).range := by
    ext f
    constructor
    · rintro ⟨g,⟨x,rfl⟩,rfl⟩
      refine ⟨e x,?_⟩
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
    · rintro ⟨x,rfl⟩
      refine ⟨MulAut.conj (e.symm x),⟨e.symm x,rfl⟩,?_⟩
      ext y
      simp [MulAut.congr_apply, MulAut.conj_apply]
  have hi := Subgroup.index_map_of_bijective (f := (MulAut.congr e).toMonoidHom)
    (MulAut.congr e).bijective (MulAut.conj : G →* MulAut G).range
  rw [he,QuaternionGroup.index_range_conj_two] at hi
  exact hi.symm

/-- Both standard quaternion generators are differences from full automorphism actions. -/
public theorem aut_difference_generators_two :
    ∃ (e f : MulAut (QuaternionGroup 2)) (x y : QuaternionGroup 2),
      x⁻¹ * e x = a 1 ∧ y⁻¹ * f y = xa 0 := by
  let p : Pairs := ⟨(a 1,xa 1),by decide⟩
  let q : Pairs := ⟨(xa 3,xa 0),by decide⟩
  refine ⟨pairAut p,pairAut q,xa 0,a 1,?_,?_⟩
  · have he := (pair_map_spec p).2.2.2
    change pairAut p (xa 0) = xa 1 at he
    rw [he]
    decide
  · have he := (pair_map_spec q).2.2.1
    change pairAut q (a 1) = xa 3 at he
    rw [he]
    decide
private theorem exists_pair_first : ∀ x : Q, x ^ 2 ≠ 1 →
    ∃ p : Pairs, p.val.1 = x := by decide

/-- Automorphisms of the quaternion group of order eight act transitively on
its elements of order four. -/
public theorem exists_mulAut_eq_of_orderOf_eq_four (x y : QuaternionGroup 2)
    (hx : orderOf x = 4) (hy : orderOf y = 4) :
    ∃ e : MulAut (QuaternionGroup 2), e x = y := by
  have hs (z : Q) (hz : orderOf z = 4) : z ^ 2 ≠ 1 := by
    intro h
    have hd := orderOf_dvd_of_pow_eq_one h
    rw [hz] at hd
    norm_num at hd
  obtain ⟨p, hp⟩ := exists_pair_first x (hs x hx)
  obtain ⟨q, hq⟩ := exists_pair_first y (hs y hy)
  have hpx : pairAut p (a 1) = x := (pair_map_spec p).2.2.1.trans hp
  have hqy : pairAut q (a 1) = y := (pair_map_spec q).2.2.1.trans hq
  refine ⟨(pairAut p).symm.trans (pairAut q), ?_⟩
  change pairAut q ((pairAut p).symm x) = y
  rw [← hpx, MulEquiv.symm_apply_apply, hqy]
private theorem pair_fixed_center : ∀ p : Pairs,
    (∀ x : Q, pairMap p.val (pairMap p.val (pairMap p.val x)) = x) →
    (∃ x : Q, pairMap p.val x ≠ x) →
    ∀ x : Q, pairMap p.val x = x → ∀ y : Q, y * x = x * y := by
  decide

/-- A nonidentity quaternion automorphism whose cube is the identity fixes only
central elements. -/
public theorem fixed_mem_center_of_cube_eq_one_ne_one
    (e : MulAut (QuaternionGroup 2)) (he : e ^ 3 = 1) (hne : e ≠ 1)
    {x : QuaternionGroup 2} (hx : e x = x) :
    x ∈ Subgroup.center (QuaternionGroup 2) := by
  have hp : ∀ y : Q, pairMap (autPair e).val y = e y := by
    intro y
    exact DFunLike.congr_fun (autEquivPairs.left_inv e) y
  have hc : ∀ y : Q,
      pairMap (autPair e).val (pairMap (autPair e).val (pairMap (autPair e).val y)) = y := by
    intro y
    simp only [hp]
    have h := DFunLike.congr_fun he y
    simpa [pow_succ, MulAut.mul_apply] using h
  have hn : ∃ y : Q, pairMap (autPair e).val y ≠ y := by
    by_contra! h
    apply hne
    ext y
    exact (hp y).symm.trans (h y)
  exact Subgroup.mem_center_iff.mpr
    (pair_fixed_center (autPair e) hc hn x ((hp x).trans hx))
private theorem pair_central_difference_inner : ∀ p : Pairs,
    (∀ x y : Q, y * (x⁻¹ * pairMap p.val x) = (x⁻¹ * pairMap p.val x) * y) →
    ∃ q : Q, ∀ x : Q, pairMap p.val x = q * x * q⁻¹ := by
  decide

/-- An automorphism of the quaternion group of order eight which acts trivially
modulo the center is inner. -/
public theorem exists_conj_of_central_difference
    (e : MulAut (QuaternionGroup 2))
    (he : ∀ x, x⁻¹ * e x ∈ Subgroup.center (QuaternionGroup 2)) :
    ∃ q : QuaternionGroup 2, e = MulAut.conj q := by
  have hp : ∀ y : Q, pairMap (autPair e).val y = e y := by
    intro y
    exact DFunLike.congr_fun (autEquivPairs.left_inv e) y
  obtain ⟨q, hq⟩ := pair_central_difference_inner (autPair e) (by
    intro x y
    rw [hp]
    exact Subgroup.mem_center_iff.mp (he x) y)
  refine ⟨q, ?_⟩
  ext x
  exact (hp x).symm.trans (hq x)
/-- Central-difference automorphisms are inner in every group equipped with an
isomorphism to the quaternion group of order eight. -/
public theorem exists_conj_of_central_difference_of_equiv
    {G : Type*} [Group G] (model : G ≃* QuaternionGroup 2)
    (e : MulAut G) (he : ∀ x, x⁻¹ * e x ∈ Subgroup.center G) :
    ∃ q : G, e = MulAut.conj q := by
  have hc : ∀ x, x⁻¹ * (MulAut.congr model e) x ∈
      Subgroup.center (QuaternionGroup 2) := by
    intro x
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨a, rfl⟩ := model.surjective x
    obtain ⟨b, rfl⟩ := model.surjective y
    have h := congrArg model (Subgroup.mem_center_iff.mp (he a) b)
    simpa [MulAut.congr_apply] using h
  obtain ⟨q, hq⟩ := exists_conj_of_central_difference (MulAut.congr model e) hc
  refine ⟨model.symm q, ?_⟩
  ext x
  apply model.injective
  have h := DFunLike.congr_fun hq (model x)
  simpa [MulAut.congr_apply, MulAut.conj_apply] using h
/-- The centrality of fixed points of a nonidentity order-three automorphism,
transported through an explicit quaternion isomorphism. -/
public theorem fixed_mem_center_of_cube_eq_one_ne_one_of_equiv
    {G : Type*} [Group G] (model : G ≃* QuaternionGroup 2)
    (e : MulAut G) (he : e ^ 3 = 1) (hne : e ≠ 1)
    {x : G} (hx : e x = x) : x ∈ Subgroup.center G := by
  have he' : (MulAut.congr model e) ^ 3 = 1 := by
    rw [← map_pow, he, map_one]
  have hne' : MulAut.congr model e ≠ 1 := by
    intro h
    apply hne
    apply (MulAut.congr model).injective
    simpa only [map_one] using h
  have hx' : (MulAut.congr model e) (model x) = model x := by
    simpa [MulAut.congr_apply] using congrArg model hx
  have hc := fixed_mem_center_of_cube_eq_one_ne_one
    (MulAut.congr model e) he' hne' hx'
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply model.injective
  simpa using Subgroup.mem_center_iff.mp hc (model y)
private theorem pair_central_difference_center : ∀ p : Pairs,
    (∀ x : Q, pairMap p.val (pairMap p.val (pairMap p.val x)) = x) →
    (∃ x : Q, pairMap p.val x ≠ x) →
    ∀ x : Q, (∀ y : Q, y * (x⁻¹ * pairMap p.val x) =
      (x⁻¹ * pairMap p.val x) * y) → ∀ y : Q, y * x = x * y := by
  decide

/-- A nonidentity quaternion automorphism whose cube is the identity fixes no
noncentral coset modulo the center. -/
public theorem mem_center_of_central_difference_of_cube_eq_one_ne_one
    (e : MulAut (QuaternionGroup 2)) (he : e ^ 3 = 1) (hne : e ≠ 1)
    {x : QuaternionGroup 2}
    (hx : x⁻¹ * e x ∈ Subgroup.center (QuaternionGroup 2)) :
    x ∈ Subgroup.center (QuaternionGroup 2) := by
  have hp : ∀ y : Q, pairMap (autPair e).val y = e y := by
    intro y
    exact DFunLike.congr_fun (autEquivPairs.left_inv e) y
  have hc : ∀ y : Q,
      pairMap (autPair e).val (pairMap (autPair e).val (pairMap (autPair e).val y)) = y := by
    intro y
    simp only [hp]
    have h := DFunLike.congr_fun he y
    simpa [pow_succ, MulAut.mul_apply] using h
  have hn : ∃ y : Q, pairMap (autPair e).val y ≠ y := by
    by_contra! h
    apply hne
    ext y
    exact (hp y).symm.trans (h y)
  apply Subgroup.mem_center_iff.mpr
  apply pair_central_difference_center (autPair e) hc hn x
  intro y
  rw [hp]
  exact Subgroup.mem_center_iff.mp hx y

/-- The order-three central-coset fixed-point result transported through a
quaternion isomorphism. -/
public theorem mem_center_of_central_difference_of_cube_eq_one_ne_one_of_equiv
    {G : Type*} [Group G] (model : G ≃* QuaternionGroup 2)
    (e : MulAut G) (he : e ^ 3 = 1) (hne : e ≠ 1)
    {x : G} (hx : x⁻¹ * e x ∈ Subgroup.center G) :
    x ∈ Subgroup.center G := by
  have he' : (MulAut.congr model e) ^ 3 = 1 := by
    rw [← map_pow, he, map_one]
  have hne' : MulAut.congr model e ≠ 1 := by
    intro h
    apply hne
    apply (MulAut.congr model).injective
    simpa only [map_one] using h
  have hx' : (model x)⁻¹ * (MulAut.congr model e) (model x) ∈
      Subgroup.center (QuaternionGroup 2) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := model.surjective y
    have h := congrArg model (Subgroup.mem_center_iff.mp hx z)
    simpa [MulAut.congr_apply] using h
  have hc := mem_center_of_central_difference_of_cube_eq_one_ne_one
    (MulAut.congr model e) he' hne' hx'
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply model.injective
  simpa using Subgroup.mem_center_iff.mp hc (model y)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
set_option synthInstance.maxSize 100000 in
private theorem pair_cubic_eighth_inner : ∀ p q : Pairs,
    (∀ x : Q, pairMap p.val (pairMap p.val (pairMap p.val x)) = x) →
    (∃ x : Q, pairMap p.val x ≠ x) →
    (∀ x : Q, (pairMap q.val)^[8] x = x) →
    (∀ x : Q, (fun y => pairMap q.val (pairMap p.val
      (pairMap q.val (pairMap p.val (pairMap p.val y)))))^[8] x = x) →
    ∃ z : Q, ∀ x : Q, pairMap q.val x = z * x * z⁻¹ := by
  decide
/-- A quaternion automorphism is inner if it and its product with its cubic
conjugate both have eighth power one. -/
public theorem exists_conj_of_eighth_powers_of_cubic
    (e f : MulAut (QuaternionGroup 2)) (he : e^3 = 1) (hne : e ≠ 1)
    (hf : f^8 = 1) (hprod : (f * (e * f * e⁻¹))^8 = 1) :
    ∃ z : QuaternionGroup 2, f = MulAut.conj z := by
  have hp : pairMap (autPair e).val = (e : Q → Q) :=
    funext (fun x => DFunLike.congr_fun (autEquivPairs.left_inv e) x)
  have hq : pairMap (autPair f).val = (f : Q → Q) :=
    funext (fun x => DFunLike.congr_fun (autEquivPairs.left_inv f) x)
  have hpow (a : MulAut Q) (ha : a^8 = 1) : ∀ x : Q, (a : Q → Q)^[8] x = x := by
    intro x
    have h := DFunLike.congr_fun ha x
    simpa [pow_succ, Function.iterate_succ_apply] using h
  have hc : ∀ x : Q, pairMap (autPair e).val
      (pairMap (autPair e).val (pairMap (autPair e).val x)) = x := by
    intro x
    rw [hp]
    have h := DFunLike.congr_fun he x
    simpa [pow_succ] using h
  have hn : ∃ x : Q, pairMap (autPair e).val x ≠ x := by
    by_contra! h
    apply hne
    ext x
    exact hp ▸ h x
  have he2 : e^2 = e⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [pow_succ] using he)
  have hfun : (fun y => pairMap (autPair f).val (pairMap (autPair e).val
      (pairMap (autPair f).val (pairMap (autPair e).val (pairMap (autPair e).val y))))) =
      ((f * (e * f * e⁻¹) : MulAut Q) : Q → Q) := by
    funext y
    rw [hp, hq, ← he2]
    simp [pow_two]
  obtain ⟨z, hz⟩ := pair_cubic_eighth_inner (autPair e) (autPair f) hc hn
    (by simpa only [hq] using hpow f hf)
    (by rw [hfun]; exact hpow _ hprod)
  refine ⟨z, ?_⟩
  ext x
  exact hq ▸ hz x
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 100000 in
private theorem pair_inverting_involution_moved : ∀ p q r : Pairs,
    (∀ x : Q, pairMap p.val (pairMap p.val (pairMap p.val x)) = x) →
    (∃ x : Q, pairMap p.val x ≠ x) →
    (∀ x : Q, (pairMap q.val (pairMap p.val x))⁻¹ *
      pairMap p.val (pairMap p.val (pairMap q.val x)) ∈ Subgroup.center Q) →
    (∀ x : Q, (pairMap r.val (pairMap p.val x))⁻¹ *
      pairMap p.val (pairMap p.val (pairMap r.val x)) ∈ Subgroup.center Q) →
    ∃ w : Pairs,
      (∀ x : Q, pairMap w.val (pairMap w.val x) = x) ∧
      (∀ x : Q, pairMap w.val (pairMap p.val x) =
        pairMap p.val (pairMap p.val (pairMap w.val x))) ∧
      (∃ x : Q, (pairMap w.val (pairMap r.val (pairMap w.val x)))⁻¹ *
        pairMap q.val x ∉ Subgroup.center Q) := by
  decide
/-- Among the three outer inverting involutions of the quaternion cubic action,
one is moved by the second factor-swap action. -/
public theorem exists_inverting_involution_moved
    (a b c : MulAut (QuaternionGroup 2)) (ha : a^3 = 1) (hane : a ≠ 1)
    (hb : ∀ x, (b (a x))⁻¹ * a (a (b x)) ∈ Subgroup.center (QuaternionGroup 2))
    (hc : ∀ x, (c (a x))⁻¹ * a (a (c x)) ∈ Subgroup.center (QuaternionGroup 2)) :
    ∃ f : MulAut (QuaternionGroup 2), f^2 = 1 ∧
      (∀ x, f (a x) = a (a (f x))) ∧
      ∃ x, (f (c (f x)))⁻¹ * b x ∉ Subgroup.center (QuaternionGroup 2) := by
  have hp : ∀ x, pairMap (autPair a).val x = a x :=
    fun x => DFunLike.congr_fun (autEquivPairs.left_inv a) x
  have hq : ∀ x, pairMap (autPair b).val x = b x :=
    fun x => DFunLike.congr_fun (autEquivPairs.left_inv b) x
  have hr : ∀ x, pairMap (autPair c).val x = c x :=
    fun x => DFunLike.congr_fun (autEquivPairs.left_inv c) x
  have hac : ∀ x, pairMap (autPair a).val
      (pairMap (autPair a).val (pairMap (autPair a).val x)) = x := by
    intro x
    simp only [hp]
    have h := DFunLike.congr_fun ha x
    simpa [pow_succ] using h
  have han : ∃ x, pairMap (autPair a).val x ≠ x := by
    by_contra! h
    apply hane
    ext x
    exact (hp x).symm.trans (h x)
  obtain ⟨w, hw2, hwanti, hwmove⟩ := pair_inverting_involution_moved
    (autPair a) (autPair b) (autPair c) hac han
    (by intro x; simpa only [hp, hq] using hb x)
    (by intro x; simpa only [hp, hr] using hc x)
  refine ⟨pairAut w, ?_, ?_, ?_⟩
  · ext x
    change pairMap w.val (pairMap w.val x) = x
    exact hw2 x
  · intro x
    change pairMap w.val (a x) = a (a (pairMap w.val x))
    simpa only [hp] using hwanti x
  · obtain ⟨x, hx⟩ := hwmove
    refine ⟨x, ?_⟩
    change (pairMap w.val (c (pairMap w.val x)))⁻¹ * b x ∉ Subgroup.center Q
    simpa only [hr, hq] using hx
end QuaternionGroup
