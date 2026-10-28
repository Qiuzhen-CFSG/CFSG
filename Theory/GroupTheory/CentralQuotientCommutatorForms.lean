module
public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The faithful commutator pairing on an elementary central quotient

Central commutators descend to a pairing on the quotient by the center.
Its common radical is zero, although its individual scalar specializations
can be degenerate. The derived group has exponent two and scalar duals
separate its points. This is the class-two pairing used in MacWilliams,
*On 2-groups with no normal abelian subgroups of rank 3*, §3, pp.366–374.
-/
open scoped commutatorElement IsMulCommutative
open Subgroup
namespace IsElementaryAbelian

public theorem derived_of_central_quotient
    {P : Type*} [Group P] (hquot : IsElementaryAbelian 2 (P ⧸ center P)) :
    IsElementaryAbelian 2 (_root_.commutator P) := by
  have hd := hquot.commutator_le_center_of_central_quotient
  let : IsMulCommutative (_root_.commutator P) := ⟨⟨fun x y =>
    Subtype.ext (mem_center_iff.mp (hd x.property) y).symm⟩⟩
  let K := (powMonoidHom 2 : center P →* center P).ker.map (center P).subtype
  have hle : _root_.commutator P ≤ K := by
    apply commutator_le.mpr
    intro x _ y _
    refine ⟨⟨⁅x,y⁆, hd (commutator_mem_commutator (mem_top x) (mem_top y))⟩, ?_, rfl⟩
    exact Subtype.ext (hquot.commutatorElement_sq_eq_one_of_central_quotient x y)
  refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
  intro x
  obtain ⟨z, hz, he⟩ := hle x.property
  apply Subtype.ext
  change (x : P) ^ 2 = 1
  have hp := congrArg Subtype.val (show z ^ 2 = 1 from hz)
  change (z : P) ^ 2 = 1 at hp
  change (z : P) = (x : P) at he
  simpa only [he] using hp

private def bracketHom {P : Type*} [Group P]
    (hd : _root_.commutator P ≤ center P) (x : P) : P →* _root_.commutator P where
  toFun y := ⟨⁅x,y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' y z := by
    apply Subtype.ext
    change ⁅x,y*z⁆ = ⁅x,y⁆ * ⁅x,z⁆
    rw [commutatorElement_mul_right_eq_mul_conj,
      mul_assoc ⁅x,y⁆ y ⁅x,z⁆,
      mem_center_iff.mp (hd (commutator_mem_commutator (mem_top x) (mem_top z))) y]
    simp only [← mul_assoc, mul_inv_cancel_right]

private theorem exists_pairing {P : Type*} [Group P]
    [IsMulCommutative (_root_.commutator P)]
    (hd : _root_.commutator P ≤ center P) :
    ∃ B : (P ⧸ center P) →* ((P ⧸ center P) →* _root_.commutator P),
      ∀ x y : P, (B (QuotientGroup.mk' (center P) x)
        (QuotientGroup.mk' (center P) y) : P) = ⁅x,y⁆ := by
  have hk (x : P) : center P ≤ (bracketHom hd x).ker := by
    intro z hz
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz x)
  let B : P →* ((P ⧸ center P) →* _root_.commutator P) := {
    toFun x := QuotientGroup.lift (center P) (bracketHom hd x) (hk x)
    map_one' := by
      apply MonoidHom.ext
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center P) q
      apply Subtype.ext
      change ⁅(1 : P), y⁆ = 1
      simp
    map_mul' x y := by
      apply MonoidHom.ext
      intro q
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (center P) q
      apply Subtype.ext
      change ⁅x*y,z⁆ = ⁅x,z⁆ * ⁅y,z⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        mem_center_iff.mp (hd (commutator_mem_commutator (mem_top y) (mem_top z))) x]
      simp only [mul_inv_cancel_right]
      exact (mem_center_iff.mp (hd (commutator_mem_commutator (mem_top y) (mem_top z))) ⁅x,z⁆).symm }
  refine ⟨QuotientGroup.lift (center P) B ?_, fun x y => rfl⟩
  intro x hx
  apply MonoidHom.ext
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center P) q
  apply Subtype.ext
  change ⁅x,y⁆ = 1
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hx y).symm

/-- Scalar alternating forms of the central commutator pairing have zero common
radical. Every automorphism fixing the center preserves all these forms. -/
public theorem exists_separating_invariant_central_quotient_forms
    {P : Type*} [Group P] [IsElementaryAbelian 2 (P ⧸ center P)] :
    ∃ forms : Set (LinearMap.BilinForm (ZMod 2) (Additive (P ⧸ center P))),
      (∀ B ∈ forms, B.IsAlt) ∧
      (∀ v, (∀ B ∈ forms, ∀ w, B v w = 0) → v = 0) ∧
      ∀ (a : MulAut P), (∀ z : center P, a z = z) →
        ∀ B ∈ forms, ∀ v w,
          B (Additive.ofMul (quotientAut (center P) a v.toMul))
            (Additive.ofMul (quotientAut (center P) a w.toMul)) = B v w := by
  let hq : IsElementaryAbelian 2 (P ⧸ center P) := inferInstance
  let := hq.derived_of_central_quotient
  obtain ⟨pairing, heval⟩ := exists_pairing hq.commutator_le_center_of_central_quotient
  let scalar (f : Module.Dual (ZMod 2) (Additive (_root_.commutator P))) :
      LinearMap.BilinForm (ZMod 2) (Additive (P ⧸ center P)) :=
    AddMonoidHom.toZModLinearMap 2 {
      toFun := fun x => AddMonoidHom.toZModLinearMap 2 {
        toFun := fun y => f (Additive.ofMul (pairing x.toMul y.toMul))
        map_zero' := by simp
        map_add' := by intros; simp }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  refine ⟨Set.range scalar, ?_, ?_, ?_⟩
  · rintro _ ⟨f, rfl⟩ v
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center P) v.toMul
    have hB : pairing v.toMul v.toMul = 1 := by
      apply Subtype.ext
      rw [← hx, heval, commutatorElement_self]
      rfl
    change f (Additive.ofMul (pairing v.toMul v.toMul)) = 0
    rw [hB]
    exact map_zero f
  · intro v hv
    have hB (w : P ⧸ center P) : pairing v.toMul w = 1 := by
      by_contra hn
      have hn' : Additive.ofMul (pairing v.toMul w) ≠ 0 := hn
      obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hn'
      exact hf (hv (scalar f) ⟨f, rfl⟩ (Additive.ofMul w))
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center P) v.toMul
    have hcenter : x ∈ center P := by
      apply mem_center_iff.mpr
      intro y
      have he := congrArg Subtype.val (hB (QuotientGroup.mk' (center P) y))
      rw [← hx, heval] at he
      exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
    exact congrArg Additive.ofMul (hx.symm.trans ((QuotientGroup.eq_one_iff x).mpr hcenter))
  · intro a ha B hB v w
    obtain ⟨f, rfl⟩ := hB
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center P) v.toMul
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center P) w.toMul
    change f (Additive.ofMul (pairing (quotientAut (center P) a v.toMul)
      (quotientAut (center P) a w.toMul))) = f (Additive.ofMul (pairing v.toMul w.toMul))
    congr 2
    apply Subtype.ext
    rw [← hx, ← hy, quotientAut_apply_mk, quotientAut_apply_mk, heval, heval,
      ← map_commutatorElement]
    exact ha ⟨⁅x,y⁆, hq.commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top x) (mem_top y))⟩

end IsElementaryAbelian
