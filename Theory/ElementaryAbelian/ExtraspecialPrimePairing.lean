module
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Commutator duality for extraspecial groups at any prime

For a finite extraspecial p-group, every homomorphism from the central
quotient to the center is commutation with an element of the group.
The commutator pairing is injective on the central quotient; evaluation
on a basis bounds the order of its dual by the order of that quotient.

This generalizes the binary argument in `ExtraspecialCommutatorPairing`.
It is the duality used in Aschbacher–Smith, Lemma A.1.23, printed p.25.
-/

open scoped IsMulCommutative commutatorElement
open Subgroup

private theorem prime_hom_card_le
    {p : ℕ} [Fact p.Prime] {X Z : Type*} [Group X] [Finite X] [IsElementaryAbelian p X]
    [Group Z] [Finite Z] [IsElementaryAbelian p Z] (hZ : Nat.card Z = p) :
    Nat.card (X →* Z) ≤ Nat.card X := by
  classical
  let b := Module.Basis.ofVectorSpace (ZMod p) (Additive X)
  let I := Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive X)
  let evaluation : (X →* Z) → (I → Z) := fun f i => f (b i).toMul
  have hinj : Function.Injective evaluation := by
    intro f g heq
    apply MonoidHom.toAdditive.injective
    apply (AddMonoidHom.toZModLinearMap_injective p)
    apply b.ext
    intro i
    exact congrArg Additive.ofMul (congrFun heq i)
  have hcard := Nat.card_le_card_of_injective evaluation hinj
  have hX : Nat.card X = p ^ Nat.card I := by
    let _ : Fintype X := Fintype.ofFinite X
    let _ : Fintype I := Fintype.ofFinite I
    simpa only [Nat.card_eq_fintype_card, Fintype.card_additive, ZMod.card] using
      Module.card_fintype b
  simpa only [Nat.card_fun, hZ, ← hX] using hcard

private theorem extraspecial_commutator_mem_center
    {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [IsExtraspecial p Y] (x y : Y) :
    ⁅x,y⁆ ∈ center Y := by
  let _ := IsExtraspecial.quotient_elementary_abelian p Y
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (center Y)) ⁅x,y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

private def centralCommutatorHom
    {p : ℕ} [Fact p.Prime] {Y : Type*} [Group Y] [IsExtraspecial p Y] (x : Y) : Y →* center Y where
  toFun y := ⟨⁅x,y⁆, extraspecial_commutator_mem_center (p := p) x y⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change ⁅x,a*b⁆ = ⁅x,a⁆ * ⁅x,b⁆
    rw [commutatorElement_mul_right_eq_mul_conj,
      mul_assoc ⁅x,a⁆ a ⁅x,b⁆,
      mem_center_iff.mp (extraspecial_commutator_mem_center (p := p) x b) a]
    simp only [← mul_assoc, mul_inv_cancel_right]

/-- Every central functional of an extraspecial group is given by commutation. -/
public theorem extraspecial_commutator_represents_hom
    {p : ℕ} [Fact p.Prime] {Q : Type*} [Group Q] [Finite Q] [IsExtraspecial p Q]
    (f : (Q ⧸ center Q) →* center Q) :
    ∃ r : Q, ∀ q : Q, (f (QuotientGroup.mk' (center Q) q) : Q) = ⁅r, q⁆ := by
  classical
  let _ := IsExtraspecial.quotient_elementary_abelian p Q
  let _ : IsElementaryAbelian p (center Q) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      simpa only [IsExtraspecial.center_order_p p Q] using (pow_card_eq_one' (x := z)) }
  have hkill (x : Q) : center Q ≤ (centralCommutatorHom (p := p) x).ker := by
    intro z hz
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz x)
  let pairing : Q →* ((Q ⧸ center Q) →* center Q) := {
    toFun x := QuotientGroup.lift (center Q) (centralCommutatorHom (p := p) x) (hkill x)
    map_one' := by
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center Q) q
      apply Subtype.ext
      change ⁅(1 : Q), y⁆ = 1
      simp
    map_mul' x y := by
      apply MonoidHom.ext
      intro q
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (center Q) q
      apply Subtype.ext
      change ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        mem_center_iff.mp (extraspecial_commutator_mem_center (p := p) y z) x]
      simp only [mul_inv_cancel_right]
      exact (mem_center_iff.mp (extraspecial_commutator_mem_center (p := p) y z) ⁅x, z⁆).symm }
  have hker : pairing.ker = center Q := by
    ext x
    change pairing x = 1 ↔ x ∈ center Q
    constructor
    · intro heq
      rw [mem_center_iff]
      intro y
      have hh := congrArg
        (fun g : (Q ⧸ center Q) →* center Q => (g (QuotientGroup.mk' (center Q) y) : Q)) heq
      change ⁅x, y⁆ = 1 at hh
      exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
    · intro hx
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center Q) q
      apply Subtype.ext
      change ⁅x, y⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hx y).symm
  let quotientPairing : (Q ⧸ center Q) →* ((Q ⧸ center Q) →* center Q) :=
    QuotientGroup.lift (center Q) pairing hker.ge
  have hinj : Function.Injective quotientPairing :=
    (QuotientGroup.injective_lift_iff (center Q) pairing hker.ge).mpr hker.symm
  let _ : Finite ((Q ⧸ center Q) →* center Q) :=
    Finite.of_injective
      (fun g : (Q ⧸ center Q) →* center Q => (g : (Q ⧸ center Q) → center Q))
      DFunLike.coe_injective
  have hsurj := (hinj.bijective_of_nat_card_le
    (prime_hom_card_le (IsExtraspecial.center_order_p p Q))).2
  obtain ⟨q, hq⟩ := hsurj f
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (center Q) q
  refine ⟨r, ?_⟩
  intro x
  exact (congrArg
    (fun g : (Q ⧸ center Q) →* center Q => (g (QuotientGroup.mk' (center Q) x) : Q)) hq).symm
