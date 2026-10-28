module

public import Theory.GroupTheory.PGroup.NormalFourAbelianBase
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Homocyclic bases invariant under centralizer automorphisms

For an abelian two-group with first omega of order four, transitivity of
its automorphism group on involutions forces the cyclic factors to have
equal order. Orbit-stabilizer and Cauchy's theorem supply an order-three
automorphism, to which the rank-two abelian structure theorem applies.

Let W be a normal elementary four in a finite two-group P without normal
elementary eights. A characteristic abelian subgroup A of C_P(W) containing
W has first omega W, so transitivity on W restricts to all involutions of A.
If A is self-centralizing in C_P(W), its ambient image is also
self-centralizing in P and is the required homocyclic normal abelian base.
Existence of a self-centralizing characteristic candidate is not asserted.

Source: the abelian invariant-base step toward Janko–Thompson,
Math. Z. 113 (1970), 1.4, printed p.386, and §6, printed p.395.
-/

open Subgroup

/-- An abelian omega-four two-group with automorphism-transitive involutions
is homocyclic. -/
public theorem IsPGroup.exists_equiv_prod_self_zmod_of_transitive_involutions
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hA : IsPGroup 2 A) (hfour : Nat.card (omega₁ A (p := 2)) = 4)
    (htrans : ∀ x y : A, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut A, a x = y) :
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty
      (A ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n)))) := by
  classical
  let O := omega₁ A (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  have hthree : Nat.card {x : A // orderOf x = 2} = 3 := by
    let e : {x : A // orderOf x = 2} ≃ {x : O // x ≠ 1} :=
      { toFun := fun x => ⟨⟨x, subset_closure (by
          simpa using (orderOf_eq_prime_iff.mp x.property).1)⟩,
          fun he => (orderOf_eq_prime_iff.mp x.property).2 (congrArg Subtype.val he)⟩
        invFun := fun x => ⟨x.val, orderOf_eq_prime
          (elemPow_eq_one_of_isElementaryAbelian _ x.val.property)
          (fun he => x.property (Subtype.ext he))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let : Fintype O := Fintype.ofFinite O
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card, show Nat.card O = 4 from hfour]
    simp
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := O) 2 (by rw [hfour]; decide)
  have hzA : orderOf (z : A) = 2 := (orderOf_coe z).trans hz
  have heq : MulAction.orbit (MulAut A) (z : A) = {x : A | orderOf x = 2} := by
    ext y
    constructor
    · intro hy
      obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.mp hy
      exact (a.orderOf_eq z).trans hzA
    · intro hy
      obtain ⟨a, ha⟩ := htrans z y hzA hy
      exact MulAction.mem_orbit_iff.mpr ⟨a, ha⟩
  have horbit : Nat.card (MulAction.orbit (MulAut A) (z : A)) = 3 := by
    rw [heq]
    exact hthree
  have hdiv : 3 ∣ Nat.card (MulAut A) := by
    refine ⟨Nat.card (MulAction.stabilizer (MulAut A) (z : A)), ?_⟩
    rw [← horbit, ← Nat.card_prod]
    exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (MulAut A) (z : A))).symm
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := MulAut A) 3 hdiv
  exact hA.exists_equiv_prod_self_zmod_of_orderOf_aut_eq_three hfour a ha

/-- Characteristic abelian overgroups of the four inherit transitivity and
therefore have equal cyclic factors. -/
public theorem Subgroup.homocyclic_of_characteristic_abelian_over_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (A : Subgroup (centralizer (W : Set P))) [A.Characteristic] [IsMulCommutative A]
    (hWA : W ≤ A.map (centralizer (W : Set P)).subtype) :
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty
      (A.map (centralizer (W : Set P)).subtype ≃*
        (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n)))) := by
  let C := centralizer (W : Set P)
  let D := A.map C.subtype
  let : D.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsMulCommutative D := Subgroup.map_isMulCommutative (H := A) C.subtype
  have hO := omega_one_eq_normal_four_of_no_normal_eight hno W D hW hWA
  have hfour : Nat.card (omega₁ D (p := 2)) = 4 := by
    have hh := congrArg (fun H : Subgroup P => Nat.card H) hO
    simpa only [card_map_of_injective D.subtype_injective, hW] using hh
  have hmem (d : D) (hd : orderOf d = 2) : (d : P) ∈ W := by
    rw [← hO]
    refine ⟨d, subset_closure ?_, rfl⟩
    change d ^ (2 ^ 1) = 1
    simpa only [pow_one, hd] using pow_orderOf_eq_one d
  have hDtrans : ∀ x y : D, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut D, a x = y := by
    let e : A ≃* D := A.equivMapOfInjective C.subtype C.subtype_injective
    intro x y hx hy
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    have hxC : orderOf (x : C) = 2 :=
      (orderOf_coe x).trans ((e.orderOf_eq x).symm.trans hx)
    have hyC : orderOf (y : C) = 2 :=
      (orderOf_coe y).trans ((e.orderOf_eq y).symm.trans hy)
    obtain ⟨a, ha⟩ := htrans x y (hmem (e x) hx) (hmem (e y) hy) hxC hyC
    refine ⟨e.symm.trans ((MulAut.characteristic A a).trans e), ?_⟩
    change e (MulAut.characteristic A a (e.symm (e x))) = e y
    rw [e.symm_apply_apply]
    exact congrArg e (Subtype.ext ha)
  exact IsPGroup.exists_equiv_prod_self_zmod_of_transitive_involutions (hP.to_subgroup D) hfour hDtrans

/-- A characteristic self-centralizing abelian subgroup of the four's centralizer
supplies a homocyclic self-centralizing normal abelian base in the ambient group. -/
public theorem IsPGroup.exists_homocyclic_base_of_characteristic_centralizer_base
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (A : Subgroup (centralizer (W : Set P))) [A.Characteristic] [IsMulCommutative A]
    (hA : centralizer (A : Set (centralizer (W : Set P))) ≤ A) :
    ∃ D : Subgroup P, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set P) ≤ D ∧
      (omega₁ D (p := 2)).map D.subtype = W ∧
      ∃ n : ℕ, 1 ≤ n ∧ Nonempty
        (D ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n)))) := by
  let C := centralizer (W : Set P)
  let D := A.map C.subtype
  let : D.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsMulCommutative D := Subgroup.map_isMulCommutative (H := A) C.subtype
  have hWD : W ≤ D := by
    intro w hw
    have hwC : w ∈ C := le_centralizer W hw
    refine ⟨⟨w, hwC⟩, hA ?_, rfl⟩
    intro a ha
    exact Subtype.ext (a.property w hw).symm
  have hDC : centralizer (D : Set P) ≤ D := by
    intro x hx
    have hxC : x ∈ C := centralizer_le hWD hx
    refine ⟨⟨x, hxC⟩, hA ?_, rfl⟩
    intro a ha
    exact Subtype.ext (hx a (mem_map_of_mem C.subtype ha))
  have hO := omega_one_eq_normal_four_of_no_normal_eight hno W D hW hWD
  exact ⟨D, hWD, inferInstance, inferInstance, hDC, hO,
    homocyclic_of_characteristic_abelian_over_four hP hno W hW htrans A hWD⟩

/-- A maximal characteristic abelian subgroup of the centralizer can be chosen
homocyclic and containing the four. Self-centrality remains a separate condition. -/
public theorem IsPGroup.exists_maximal_characteristic_abelian_homocyclic_in_four_centralizer
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y) :
    ∃ A : Subgroup (centralizer (W : Set P)), A.Characteristic ∧ IsMulCommutative A ∧
      W ≤ A.map (centralizer (W : Set P)).subtype ∧
      (∀ A' : Subgroup (centralizer (W : Set P)), A'.Characteristic →
        IsMulCommutative A' → A ≤ A' → A' = A) ∧
      ∃ n : ℕ, 1 ≤ n ∧ Nonempty
        (A.map (centralizer (W : Set P)).subtype ≃*
          (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n)))) := by
  classical
  let C := centralizer (W : Set P)
  let good : Subgroup C → Prop := fun A => A.Characteristic ∧ IsMulCommutative A
  obtain ⟨A, hZA, hmax⟩ := Finite.exists_le_maximal (p := good)
    (a := center C) ⟨inferInstance, inferInstance⟩
  let : A.Characteristic := hmax.1.1
  let : IsMulCommutative A := hmax.1.2
  have hWA : W ≤ A.map C.subtype := by
    intro w hw
    have hwC : w ∈ C := le_centralizer W hw
    refine ⟨⟨w, hwC⟩, hZA (mem_center_iff.mpr ?_), rfl⟩
    intro c
    exact Subtype.ext (c.property w hw).symm
  refine ⟨A, inferInstance, inferInstance, hWA, ?_,
    homocyclic_of_characteristic_abelian_over_four hP hno W hW htrans A hWA⟩
  intro A' hAc hAa hAA
  exact le_antisymm (hmax.2 ⟨hAc, hAa⟩ hAA) hAA
