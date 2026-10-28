module

public import Theory.GroupTheory.QuaternionCentralProductIntrinsic
public import Theory.GroupTheory.QuaternionCentralProductDiagonal
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The intrinsic quadratic space of a quaternion central product

Squaring on the actual quotient by the center gives a binary quadratic form.
Its polar form is the commutator, so its radical is zero. The quotient has
order sixteen and hence dimension four. Matching the two quaternion factors
constructs an elementary eight containing the center; its quotient is a
singular plane. Thus the form has plus type.

The linear isometry subgroup retains precisely the original center-valued
square map. The actual automorphism action is supplied as a homomorphism into
this subgroup, with its action on every quotient vector specified. This file
does not assert the order or a coordinate identification of the full group.

Source: the Q₈ * Q₈ orthogonal-action step in Aschbacher–Smith,
Lemma 14.2.21, refs/quasithin.pdf, printed p.988, PDF p.1005.
-/

public section

open scoped IsMulCommutative commutatorElement
namespace Subgroup.QuaternionCentralProductData
variable {Q : Type*} [Group Q] [Finite Q] (d : QuaternionCentralProductData Q)
/-- The additive central quotient, indexed by its intrinsic factor data. -/
@[expose, reducible] def SquareSpace (_d : QuaternionCentralProductData Q) := Additive (Q ⧸ center Q)

instance squareSpaceAddCommGroup : AddCommGroup d.SquareSpace := by
  letI := d.quotient_elementary
  exact inferInstanceAs (AddCommGroup (Additive (Q ⧸ center Q)))

instance squareSpaceModule : Module (ZMod 2) d.SquareSpace := by
  letI := d.quotient_elementary
  exact inferInstanceAs (Module (ZMod 2) (Additive (Q ⧸ center Q)))

@[expose] instance squareSpaceFinite : Finite d.SquareSpace := inferInstanceAs (Finite (Additive (Q ⧸ center Q)))

include d

/-- Identify the actual center with the multiplicative tag of the binary field. -/
noncomputable def centerCoordinate : center Q ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq d.center_card (by simp)

@[simp] theorem centerCoordinate_eq_zero_iff (z : center Q) :
    (d.centerCoordinate z).toAdd = 0 ↔ z = 1 := d.centerCoordinate.map_eq_one_iff

@[simp] theorem centerCoordinate_eq_one_iff (z : center Q) :
    (d.centerCoordinate z).toAdd = 1 ↔ z ≠ 1 := by
  have binary : ∀ a : ZMod 2, a = 1 ↔ a ≠ 0 := by decide
  rw [binary, ne_eq, d.centerCoordinate_eq_zero_iff]

/-- The literal square map, written with binary scalar values. -/
noncomputable def binarySquare (v : d.SquareSpace) : ZMod 2 :=
  (d.centerCoordinate (d.square v.toMul)).toAdd

@[simp] theorem binarySquare_zero : d.binarySquare 0 = 0 := by
  change (d.centerCoordinate (d.square (QuotientGroup.mk' (center Q) 1))).toAdd = 0
  have h : d.square (QuotientGroup.mk' (center Q) 1) = 1 :=
    Subtype.ext (by rw [d.square_mk, one_pow]; rfl)
  rw [h, map_one]
  rfl

theorem binarySquare_mk (x : Q) :
    d.binarySquare (Additive.ofMul (QuotientGroup.mk' (center Q) x)) =
      (d.centerCoordinate ⟨x ^ 2, d.square_mem_center x⟩).toAdd := by
  change (d.centerCoordinate (d.square (QuotientGroup.mk' (center Q) x))).toAdd = _
  rw [show d.square (QuotientGroup.mk' (center Q) x) =
    ⟨x ^ 2, d.square_mem_center x⟩ from Subtype.ext (d.square_mk x)]

theorem commutator_mem_center (x y : Q) : ⁅x,y⁆ ∈ center Q := by
  let _ := d.quotient_elementary
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (center Q)) ⁅x,y⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

private theorem square_mul (x y : Q) :
    (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x,y⁆ := by
  symm
  calc
    x ^ 2 * y ^ 2 * ⁅x,y⁆ = ⁅x,y⁆ * (x ^ 2 * y ^ 2) :=
      mem_center_iff.mp (d.commutator_mem_center x y) _
    _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
      simp only [commutatorElement_def, mul_assoc]
    _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by
      rw [mem_center_iff.mp (d.square_mem_center x)]
    _ = (x * y) ^ 2 := by simp only [pow_two]; group

theorem binarySquare_polar_mk (x y : Q) :
    QuadraticMap.polar d.binarySquare
      (Additive.ofMul (QuotientGroup.mk' (center Q) x))
      (Additive.ofMul (QuotientGroup.mk' (center Q) y)) =
        (d.centerCoordinate ⟨⁅x,y⁆, d.commutator_mem_center x y⟩).toAdd := by
  have hs : (⟨(x*y)^2, d.square_mem_center (x*y)⟩ : center Q) =
      ⟨x^2, d.square_mem_center x⟩ * ⟨y^2, d.square_mem_center y⟩ *
        ⟨⁅x,y⁆, d.commutator_mem_center x y⟩ := Subtype.ext (d.square_mul x y)
  change d.binarySquare (Additive.ofMul (QuotientGroup.mk' (center Q) (x*y))) -
    d.binarySquare (Additive.ofMul (QuotientGroup.mk' (center Q) x)) -
    d.binarySquare (Additive.ofMul (QuotientGroup.mk' (center Q) y)) = _
  rw [d.binarySquare_mk, d.binarySquare_mk, d.binarySquare_mk, hs, map_mul (d.centerCoordinate), map_mul (d.centerCoordinate)]
  simp only [toAdd_mul]
  abel

private theorem binarySquare_polar_add (u v w : d.SquareSpace) :
    QuadraticMap.polar d.binarySquare (u + v) w =
      QuadraticMap.polar d.binarySquare u w + QuadraticMap.polar d.binarySquare v w := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center Q) u.toMul
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (center Q) v.toMul
  obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (center Q) w.toMul
  have hu : u = Additive.ofMul (QuotientGroup.mk' (center Q) x) := congrArg Additive.ofMul hx.symm
  have hv : v = Additive.ofMul (QuotientGroup.mk' (center Q) y) := congrArg Additive.ofMul hy.symm
  have hw : w = Additive.ofMul (QuotientGroup.mk' (center Q) z) := congrArg Additive.ofMul hz.symm
  subst u v w
  have hc : ⁅x*y,z⁆ = ⁅x,z⁆ * ⁅y,z⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,
      mem_center_iff.mp (d.commutator_mem_center y z) x]
    simp only [mul_inv_cancel_right]
    exact (mem_center_iff.mp (d.commutator_mem_center y z) ⁅x,z⁆).symm
  change QuadraticMap.polar d.binarySquare
    (Additive.ofMul (QuotientGroup.mk' (center Q) (x*y))) _ = _
  rw [d.binarySquare_polar_mk, d.binarySquare_polar_mk, d.binarySquare_polar_mk]
  have he : (⟨⁅x*y,z⁆, d.commutator_mem_center (x*y) z⟩ : center Q) =
      ⟨⁅x,z⁆, d.commutator_mem_center x z⟩ * ⟨⁅y,z⁆, d.commutator_mem_center y z⟩ :=
    Subtype.ext hc
  rw [he, map_mul (d.centerCoordinate)]
  rfl

/-- The binary quadratic form obtained from squaring in the group. -/
noncomputable def quadraticForm : QuadraticForm (ZMod 2) d.SquareSpace :=
  QuadraticMap.ofPolar d.binarySquare
    (by
      intro a x
      have binary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      rcases binary a with rfl | rfl <;> simp)
    d.binarySquare_polar_add
    (by
      intro a x y
      have binary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      rcases binary a with rfl | rfl <;> simp [QuadraticMap.polar])

@[simp] theorem quadraticForm_apply (v : d.SquareSpace) :
    d.quadraticForm v = d.binarySquare v := by rfl

theorem polarBilin_mk (x y : Q) :
    d.quadraticForm.polarBilin
      (Additive.ofMul (QuotientGroup.mk' (center Q) x))
      (Additive.ofMul (QuotientGroup.mk' (center Q) y)) =
        (d.centerCoordinate ⟨⁅x,y⁆, d.commutator_mem_center x y⟩).toAdd :=
  d.binarySquare_polar_mk x y

/-- The radical is zero because a commuting representative is central. -/
theorem polarBilin_nondegenerate : d.quadraticForm.polarBilin.Nondegenerate := by
  have hsep : d.quadraticForm.polarBilin.SeparatingLeft := by
    intro v hv
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center Q) v.toMul
    have he : v = Additive.ofMul (QuotientGroup.mk' (center Q) x) := congrArg Additive.ofMul hx.symm
    subst v
    have hcentral : x ∈ center Q := by
      apply mem_center_iff.mpr
      intro y
      have hh := hv (Additive.ofMul (QuotientGroup.mk' (center Q) y))
      rw [d.polarBilin_mk] at hh
      have hc : (⟨⁅x,y⁆, d.commutator_mem_center x y⟩ : center Q) = 1 := by
        apply d.centerCoordinate.injective
        exact (congrArg Multiplicative.ofAdd hh).trans d.centerCoordinate.map_one.symm
      exact (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hc)).symm
    exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff x).mpr hcentral)
  refine ⟨hsep, ?_⟩
  intro v hv
  apply hsep v
  intro w
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  exact hv w

/-- The intrinsic quadratic space has dimension four. -/
theorem quotient_finrank : Module.finrank (ZMod 2) d.SquareSpace = 4 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := d.SquareSpace)
  have hq : Nat.card d.SquareSpace = 16 := d.quotient_card
  rw [hq, Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm

theorem quadraticForm_invariant (a : MulAut Q) (v : Q ⧸ center Q) :
    d.quadraticForm (Additive.ofMul (quotientAut (center Q) a v)) =
      d.quadraticForm (Additive.ofMul v) := by
  change (d.centerCoordinate (d.square (quotientAut (center Q) a v))).toAdd = _
  rw [d.square_invariant]
  rfl

/-- A totally singular plane in the actual central quotient. -/
theorem exists_singular_plane :
    ∃ W : Submodule (ZMod 2) d.SquareSpace,
      Module.finrank (ZMod 2) W = 2 ∧ ∀ v ∈ W, d.quadraticForm v = 0 := by
  obtain ⟨eL⟩ := d.left_model
  obtain ⟨eR⟩ := d.right_model
  let E := quaternionDiagonal d.left d.right (eL.trans eR.symm) d.commute
  obtain ⟨hE, hEcard, hZE, _⟩ := quaternion_diagonal_elementary_eight
    d.left d.right eL (eL.trans eR.symm) d.intersection_card d.commute
  have hz : center Q ≤ E := by rw [d.center_eq]; exact hZE
  let π := QuotientGroup.mk' (center Q)
  let H := E.map π
  have hindex : H.index = E.index := E.index_map_eq
    (QuotientGroup.mk'_surjective (center Q)) (by rw [QuotientGroup.ker_mk']; exact hz)
  have hEindex : E.index = 4 := by
    have he := E.card_mul_index
    rw [hEcard, d.card] at he
    omega
  have hHcard : Nat.card H = 4 := by
    have hh := H.card_mul_index
    rw [hindex, hEindex, d.quotient_card] at hh
    omega
  let W : Submodule (ZMod 2) d.SquareSpace := {
    carrier := {v | v.toMul ∈ H}
    zero_mem' := H.one_mem
    add_mem' := fun hx hy => H.mul_mem hx hy
    smul_mem' := by
      intro a v hv
      have binary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      rcases binary a with rfl | rfl
      · rw [zero_smul]
        exact H.one_mem
      · simpa only [one_smul] using hv }
  have hcW : Nat.card W = 4 := by
    let e : W ≃ H := {
      toFun := fun v => ⟨v.val.toMul, v.property⟩
      invFun := fun v => ⟨Additive.ofMul v.val, v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans hHcard
  refine ⟨W, ?_, ?_⟩
  · have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [hcW, Nat.card_zmod] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm
  · intro v hv
    obtain ⟨x, hx, he⟩ := hv
    have hs : x ^ 2 = 1 := by
      let _ := hE
      exact elemPow_eq_one_of_isElementaryAbelian x hx
    have hev : v = Additive.ofMul (π x) := congrArg Additive.ofMul he.symm
    rw [hev, d.quadraticForm_apply, d.binarySquare_mk]
    have hsq : (⟨x ^ 2, d.square_mem_center x⟩ : center Q) = 1 := Subtype.ext hs
    rw [hsq, map_one]
    rfl

/-- The literal quotient action, viewed as binary linear automorphisms. -/
noncomputable def quotientLinearAction : MulAut Q →* (d.SquareSpace ≃ₗ[ZMod 2] d.SquareSpace) where
  toFun a := {
    toFun := fun v => Additive.ofMul (quotientAut (center Q) a v.toMul)
    invFun := fun v => Additive.ofMul ((quotientAut (center Q) a).symm v.toMul)
    left_inv := fun v => (quotientAut (center Q) a).symm_apply_apply v
    right_inv := fun v => (quotientAut (center Q) a).apply_symm_apply v
    map_add' := fun v w => congrArg Additive.ofMul (map_mul (quotientAut (center Q) a) v.toMul w.toMul)
    map_smul' := by
      intro r v
      have binary : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
      rcases binary r with rfl | rfl
      · simp only [RingHom.id_apply, zero_smul]
        change Additive.ofMul (quotientAut (center Q) a 1) = Additive.ofMul 1
        exact congrArg Additive.ofMul (map_one (quotientAut (center Q) a))
      · simp only [one_smul, RingHom.id_apply] }
  map_one' := by
    ext v
    exact congrArg (fun e : MulAut (Q ⧸ center Q) => Additive.ofMul (e v.toMul))
      (map_one (quotientAut (center Q)))
  map_mul' a b := by
    ext v
    exact congrArg (fun e : MulAut (Q ⧸ center Q) => Additive.ofMul (e v.toMul))
      (map_mul (quotientAut (center Q)) a b)

@[simp] theorem quotientLinearAction_apply (a : MulAut Q) (v : Q ⧸ center Q) :
    d.quotientLinearAction a (Additive.ofMul v) =
      Additive.ofMul (quotientAut (center Q) a v) := by rfl

/-- The full linear square-form isometry group on the literal central quotient. -/
@[expose] noncomputable def squareIsometries : Subgroup (d.SquareSpace ≃ₗ[ZMod 2] d.SquareSpace) :=
  d.quadraticForm.isometrySubgroup

@[simp] theorem mem_squareIsometries (g : d.SquareSpace ≃ₗ[ZMod 2] d.SquareSpace) :
    g ∈ d.squareIsometries ↔ ∀ v, d.quadraticForm (g v) = d.quadraticForm v :=
  QuadraticMap.mem_isometrySubgroup d.quadraticForm g

/-- Preservation of the scalar form is exactly preservation of the center-valued square map. -/
theorem mem_squareIsometries_iff_square (g : d.SquareSpace ≃ₗ[ZMod 2] d.SquareSpace) :
    g ∈ d.squareIsometries ↔
      ∀ v : Q ⧸ center Q, d.square (g (Additive.ofMul v)).toMul = d.square v := by
  rw [d.mem_squareIsometries]
  constructor
  · intro h v
    apply d.centerCoordinate.injective
    exact congrArg Multiplicative.ofAdd (h (Additive.ofMul v))
  · intro h v
    change (d.centerCoordinate (d.square (g v).toMul)).toAdd =
      (d.centerCoordinate (d.square v.toMul)).toAdd
    exact congrArg (fun z => (d.centerCoordinate z).toAdd) (h v.toMul)

/-- The actual automorphism action lands in the full square-form isometry group. -/
noncomputable def squareIsometryAction : MulAut Q →* d.squareIsometries :=
  d.quotientLinearAction.codRestrict d.squareIsometries
    (fun a => (d.mem_squareIsometries _).mpr
      (fun v => d.quadraticForm_invariant a v.toMul))

@[simp] theorem squareIsometryAction_apply (a : MulAut Q) (v : Q ⧸ center Q) :
    (d.squareIsometryAction a).val (Additive.ofMul v) =
      Additive.ofMul (quotientAut (center Q) a v) := by rfl

end Subgroup.QuaternionCentralProductData
