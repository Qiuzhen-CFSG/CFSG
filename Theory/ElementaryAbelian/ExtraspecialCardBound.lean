module
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index

/-!
# Elementary subgroup size in an extraspecial two-group

An elementary abelian subgroup E containing the center of a finite extraspecial
two-group Y satisfies |E|² ≤ 2|Y|. The subgroup and ambient extraspecial group
are retained literally; no chosen symplectic model or maximality assumption
is needed. In particular, an ambient group of order 512 gives |E| ≤ 32.

All commutators of Y are central. Since E contains the center, E is normal and
Y/E is elementary abelian. For each e in E, the commutator map y ↦ [e,y]
factors through Y/E because E is abelian. These maps form a homomorphism
from E to Hom(Y/E,Z(Y)); its kernel is exactly Z(Y), restricted to E.
Evaluation on a binary basis bounds the number of such homomorphisms by
|Y/E|, since the center has order two. The kernel/range and quotient order
identities give the stated square bound.

This source-neutral extraspecial pairing argument supplies the upper bound
in Stellmacher (8.6), between (18) and (19), Journal of Algebra 190 (1997),
printed p.45. The graph application supplies the actual extraspecial group
and the center-containing elementary intersection separately.
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

/-- The square of the order of a center-containing elementary subgroup is
at most twice the order of the extraspecial ambient two-group. -/
public theorem extraspecial_two_elementary_card_sq_le
    {Y : Type*} [Group Y] [Finite Y] [IsExtraspecial 2 Y]
    (E : Subgroup Y) [IsElementaryAbelian 2 E]
    (hZE : center Y ≤ E) : (Nat.card E)^2 ≤ 2 * Nat.card Y := by
  classical
  let _ := IsExtraspecial.quotient_elementary_abelian 2 Y
  let _ : E.Normal := ⟨fun x hx g => by
    have heq : g*x*g⁻¹ = ⁅g,x⁆*x := by simp [commutatorElement_def, mul_assoc]
    rw [heq]
    exact E.mul_mem (hZE (extraspecial_commutator_mem_center g x)) hx⟩
  let _ : IsElementaryAbelian 2 (center Y) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (z : Y) (hZE z.property) }
  let _ : IsElementaryAbelian 2 (Y ⧸ E) := {
    toIsMulCommutative := ⟨⟨fun x y => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective E x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective E y
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr
        (hZE (extraspecial_commutator_mem_center a b))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective E x
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      apply hZE
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (center Y)) (a^2) = 1
      rw [map_pow]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (Y ⧸ center Y)) _ }
  have hkill (e : E) : E ≤ (centralCommutatorHom (e : Y)).ker := by
    intro x hx
    change (⟨⁅(e : Y),x⁆, _⟩ : center Y) = 1
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (congrArg Subtype.val (mul_comm e (⟨x,hx⟩ : E)))
  let pairing : E →* ((Y ⧸ E) →* center Y) := {
    toFun e := QuotientGroup.lift E (centralCommutatorHom (e : Y)) (hkill e)
    map_one' := by
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective E q
      apply Subtype.ext
      change ⁅(1 : Y),y⁆ = 1
      simp
    map_mul' e f := by
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective E q
      apply Subtype.ext
      change ⁅(e : Y)*(f : Y),y⁆ = ⁅(e : Y),y⁆ * ⁅(f : Y),y⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        mem_center_iff.mp (extraspecial_commutator_mem_center (f : Y) y) (e : Y)]
      simp only [mul_inv_cancel_right]
      exact (mem_center_iff.mp (extraspecial_commutator_mem_center (f : Y) y) ⁅(e : Y),y⁆).symm }
  have hker : pairing.ker = (center Y).subgroupOf E := by
    ext e
    change pairing e = 1 ↔ (e : Y) ∈ center Y
    constructor
    · intro heq
      rw [mem_center_iff]
      intro y
      have heval := congrArg (fun f : (Y ⧸ E) →* center Y => (f (QuotientGroup.mk' E y) : Y)) heq
      change ⁅(e : Y),y⁆ = 1 at heval
      exact (commutatorElement_eq_one_iff_mul_comm.mp heval).symm
    · intro he
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective E q
      apply Subtype.ext
      change ⁅(e : Y),y⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp he y).symm
  have hkerCard : Nat.card pairing.ker = 2 := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hZE).toEquiv]
    exact IsExtraspecial.center_order_p 2 Y
  let _ : Finite ((Y ⧸ E) →* center Y) :=
    Finite.of_injective (fun f : (Y ⧸ E) →* center Y => (f : (Y ⧸ E) → center Y))
      DFunLike.coe_injective
  have hrange : Nat.card pairing.range ≤ Nat.card (Y ⧸ E) :=
    (Nat.card_le_card_of_injective pairing.range.subtype pairing.range.subtype_injective).trans
      (binary_hom_card_le (IsExtraspecial.center_order_p 2 Y))
  have hpair := pairing.ker.card_mul_index
  rw [Subgroup.index_ker, hkerCard] at hpair
  have hquot := E.card_mul_index
  rw [Subgroup.index_eq_card] at hquot
  nlinarith
