module
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Commutator duality for extraspecial two-groups

In a finite extraspecial two-group Q, every homomorphism from Q/Z(Q) to
Z(Q) has the form qZ(Q) ↦ [r,q] for some r in Q. The group and its center
are kept literal; no symplectic coordinates or chosen central generator
are required.

Commutators are central and multiplicative in each variable. They give a
homomorphism Q/Z(Q) → Hom(Q/Z(Q),Z(Q)), whose kernel is trivial by the
definition of the center. Evaluation on a binary basis bounds the size of
the target by |Q/Z(Q)|, because |Z(Q)|=2. Thus this homomorphism is also
surjective, which gives the required representative.

This standard extraspecial duality supplies the inner correction in the
suitable-lift interpretation of Stellmacher (8.6)(c3), printed p.41. The
construction follows the central-commutator and binary-basis arguments in
`ExtraspecialCardBound`; the action and fixed-space order32 application are
separate results.
-/

open scoped IsMulCommutative commutatorElement
open Subgroup

private theorem binary_hom_card_le
    {X Z : Type*} [Group X] [Finite X] [IsElementaryAbelian 2 X]
    [Group Z] [Finite Z] [IsElementaryAbelian 2 Z] (hZ : Nat.card Z = 2) :
    Nat.card (X →* Z) ≤ Nat.card X := by
  classical
  let b := Module.Basis.ofVectorSpace (ZMod 2) (Additive X)
  let I := Module.Basis.ofVectorSpaceIndex (ZMod 2) (Additive X)
  let evaluation : (X →* Z) → (I → Z) := fun f i => f (b i).toMul
  have hinj : Function.Injective evaluation := by
    intro f g heq
    apply MonoidHom.toAdditive.injective
    apply (AddMonoidHom.toZModLinearMap_injective 2)
    apply b.ext
    intro i
    exact congrArg Additive.ofMul (congrFun heq i)
  have hcard := Nat.card_le_card_of_injective evaluation hinj
  have hX : Nat.card X = 2 ^ Nat.card I := by
    let _ : Fintype X := Fintype.ofFinite X
    let _ : Fintype I := Fintype.ofFinite I
    simpa only [Nat.card_eq_fintype_card, Fintype.card_additive, ZMod.card] using
      Module.card_fintype b
  simpa only [Nat.card_fun, hZ, ← hX] using hcard

private theorem extraspecial_commutator_mem_center
    {Y : Type*} [Group Y] [IsExtraspecial 2 Y] (x y : Y) :
    ⁅x,y⁆ ∈ center Y := by
  let _ := IsExtraspecial.quotient_elementary_abelian 2 Y
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (center Y)) ⁅x,y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

private def centralCommutatorHom
    {Y : Type*} [Group Y] [IsExtraspecial 2 Y] (x : Y) : Y →* center Y where
  toFun y := ⟨⁅x,y⁆, extraspecial_commutator_mem_center x y⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change ⁅x,a*b⁆ = ⁅x,a⁆ * ⁅x,b⁆
    rw [commutatorElement_mul_right_eq_mul_conj,
      mul_assoc ⁅x,a⁆ a ⁅x,b⁆,
      mem_center_iff.mp (extraspecial_commutator_mem_center x b) a]
    simp only [← mul_assoc, mul_inv_cancel_right]

/-- Every central functional of an extraspecial binary group is given by commutation. -/
public theorem extraspecial_two_commutator_represents_hom
    {Q : Type*} [Group Q] [Finite Q] [IsExtraspecial 2 Q]
    (f : (Q ⧸ center Q) →* center Q) :
    ∃ r : Q, ∀ q : Q, (f (QuotientGroup.mk' (center Q) q) : Q) = ⁅r, q⁆ := by
  classical
  let _ := IsExtraspecial.quotient_elementary_abelian 2 Q
  let _ : IsElementaryAbelian 2 (center Q) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      simpa only [IsExtraspecial.center_order_p 2 Q] using (pow_card_eq_one' (x := z)) }
  have hkill (x : Q) : center Q ≤ (centralCommutatorHom x).ker := by
    intro z hz
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz x)
  let pairing : Q →* ((Q ⧸ center Q) →* center Q) := {
    toFun x := QuotientGroup.lift (center Q) (centralCommutatorHom x) (hkill x)
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
        mem_center_iff.mp (extraspecial_commutator_mem_center y z) x]
      simp only [mul_inv_cancel_right]
      exact (mem_center_iff.mp (extraspecial_commutator_mem_center y z) ⁅x, z⁆).symm }
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
    (binary_hom_card_le (IsExtraspecial.center_order_p 2 Q))).2
  obtain ⟨q, hq⟩ := hsurj f
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (center Q) q
  refine ⟨r, ?_⟩
  intro x
  exact (congrArg
    (fun g : (Q ⧸ center Q) →* center Q => (g (QuotientGroup.mk' (center Q) x) : Q)) hq).symm
