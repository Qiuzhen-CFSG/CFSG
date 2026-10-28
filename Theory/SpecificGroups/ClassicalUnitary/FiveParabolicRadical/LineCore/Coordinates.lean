module

public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.Frattini.BinarySquares
public import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Coordinates for the line radical of a five-dimensional unitary group

In a Witt basis with Gram matrix consisting of a hyperbolic pair and an
identity three-space, the upper unipotent matrices have coordinates `(v,t)`
with `t + conj t = Σ conj(vᵢ) vᵢ`. Their multiplication has cross term
`Σ conj(vᵢ) wᵢ`. We construct this group and compute its squares and commutators.
A trace-one scalar gives lifts of all vectors, proves that its center is exactly
the scalar subgroup and that every central element is a commutator. In a finite
field its Frattini subgroup is also its center. Explicit set equivalences give
its order and center order. Isometries of the middle space act by automorphisms.

The identification with the projective line parabolic's canonical two-core is
separate: this module supplies the coordinate group, not that identification.

Source: the classical unitary parabolic calculation used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.11--12(7), printed pp.262--264.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups
open scoped commutatorElement
namespace Theory.SpecificGroups.UnitaryFive.LineCore
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

def pairing (v w : Fin 3 → F) : F := ∑ i, J.conj (v i) * w i

@[simp] theorem pairing_zero_left (w : Fin 3 → F) : pairing J 0 w = 0 := by
  simp [pairing]
@[simp] theorem pairing_zero_right (v : Fin 3 → F) : pairing J v 0 = 0 := by
  simp [pairing]
theorem pairing_add_left (u v w : Fin 3 → F) :
    pairing J (u + v) w = pairing J u w + pairing J v w := by
  simp [pairing, add_mul, Finset.sum_add_distrib]
theorem pairing_add_right (u v w : Fin 3 → F) :
    pairing J u (v + w) = pairing J u v + pairing J u w := by
  simp [pairing, mul_add, Finset.sum_add_distrib]
@[simp] theorem conj_pairing (v w : Fin 3 → F) :
    J.conj (pairing J v w) = pairing J w v := by
  simp only [pairing, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [J.conj_involutive, mul_comm]

@[ext] structure Coord where
  vector : Fin 3 → F
  scalar : F
  trace_eq : scalar + J.conj scalar = pairing J vector vector

namespace Coord
variable {J}
instance : One (Coord J) := ⟨⟨0, 0, by simp⟩⟩
instance : Mul (Coord J) := ⟨fun x y =>
  ⟨x.vector + y.vector, x.scalar + y.scalar + pairing J x.vector y.vector, by
    rw [map_add, map_add, conj_pairing, pairing_add_left, pairing_add_right,
      pairing_add_right]
    linear_combination x.trace_eq + y.trace_eq⟩⟩
instance : Inv (Coord J) := ⟨fun x =>
  ⟨x.vector, J.conj x.scalar, by
    rw [J.conj_involutive, add_comm]
    exact x.trace_eq⟩⟩
@[simp] theorem one_vector : (1 : Coord J).vector = 0 := rfl
@[simp] theorem one_scalar : (1 : Coord J).scalar = 0 := rfl
@[simp] theorem mul_vector (x y : Coord J) : (x * y).vector = x.vector + y.vector := rfl
@[simp] theorem mul_scalar (x y : Coord J) :
    (x * y).scalar = x.scalar + y.scalar + pairing J x.vector y.vector := rfl
@[simp] theorem inv_vector (x : Coord J) : x⁻¹.vector = x.vector := rfl
@[simp] theorem inv_scalar (x : Coord J) : x⁻¹.scalar = J.conj x.scalar := rfl

variable [CharP F 2]
instance : Group (Coord J) := by
  apply Group.ofLeftAxioms
  · intro x y z
    apply Coord.ext
    · simp only [mul_vector, add_assoc]
    · simp only [mul_scalar, mul_vector, pairing_add_left, pairing_add_right]
      ring
  · intro x
    apply Coord.ext <;> simp
  · intro x
    apply Coord.ext
    · ext i
      simp [CharTwo.add_self_eq_zero]
    · simp only [mul_scalar, inv_scalar, inv_vector, one_scalar, ← x.trace_eq]
      simp [add_comm, CharTwo.add_self_eq_zero]

@[simp] theorem square_vector (x : Coord J) : (x ^ 2).vector = 0 := by
  ext i
  simp [pow_two, CharTwo.add_self_eq_zero]
@[simp] theorem square_scalar (x : Coord J) : (x ^ 2).scalar = pairing J x.vector x.vector := by
  simp [pow_two, CharTwo.add_self_eq_zero]
theorem fourth_power (x : Coord J) : x ^ 4 = 1 := by
  have h : (4 : ℕ) = 2 * 2 := rfl
  rw [h, pow_mul]
  apply Coord.ext <;> simp

theorem isPGroup : IsPGroup 2 (Coord J) := by
  intro x
  exact ⟨2, fourth_power x⟩

@[simp] theorem commutator_vector (x y : Coord J) : ⁅x, y⁆.vector = 0 := by
  ext i
  simp only [commutatorElement_def, mul_vector, inv_vector, Pi.add_apply, Pi.zero_apply]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (x.vector i + y.vector i) * h2

theorem commutator_scalar (x y : Coord J) :
    ⁅x, y⁆.scalar = pairing J x.vector y.vector + pairing J y.vector x.vector := by
  simp only [commutatorElement_def, mul_scalar, mul_vector, inv_vector, inv_scalar,
    pairing_add_left]
  rw [← x.trace_eq, ← y.trace_eq]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (x.scalar + y.scalar + J.conj x.scalar + J.conj y.scalar +
    pairing J x.vector y.vector) * h2

/-- A lift of each vector, using a scalar of trace one. -/
def liftVector (c : F) (hc : c + J.conj c = 1) (v : Fin 3 → F) : Coord J :=
  ⟨v, c * pairing J v v, by
    rw [map_mul, conj_pairing, ← add_mul, hc, one_mul]⟩

omit [CharP F 2] in
@[simp] theorem liftVector_vector (c : F) (hc : c + J.conj c = 1) (v : Fin 3 → F) :
    (liftVector c hc v : Coord J).vector = v := rfl

/-- Elements with zero vector coordinate are central. -/
theorem mem_center_of_vector_eq_zero (x : Coord J) (hx : x.vector = 0) :
    x ∈ Subgroup.center (Coord J) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Coord.ext <;> simp [hx, add_comm]

end Coord

variable [CharP F 2]
omit [CharP F 2] in
@[simp] theorem pairing_single_right (v : Fin 3 → F) (i : Fin 3) (a : F) :
    pairing J v (Pi.single i a) = J.conj (v i) * a := by
  classical
  simp [pairing, Pi.single_apply, apply_ite]
omit [CharP F 2] in
@[simp] theorem pairing_single_left (w : Fin 3 → F) (i : Fin 3) (a : F) :
    pairing J (Pi.single i a) w = J.conj a * w i := by
  classical
  simp [pairing, Pi.single_apply, apply_ite]

namespace Coord
variable {J}
theorem mem_center_iff_vector_eq_zero (c : F) (hc : c + J.conj c = 1) (x : Coord J) :
    x ∈ Subgroup.center (Coord J) ↔ x.vector = 0 := by
  refine ⟨?_, mem_center_of_vector_eq_zero x⟩
  intro hx
  ext i
  let y := liftVector c hc (Pi.single i (c * x.vector i))
  have hcomm : ⁅x, y⁆ = 1 := by
    rw [commutatorElement_def, ← Subgroup.mem_center_iff.mp hx y]
    group
  have h := congrArg Coord.scalar hcomm
  rw [commutator_scalar, one_scalar] at h
  change pairing J x.vector (Pi.single i (c * x.vector i)) +
    pairing J (Pi.single i (c * x.vector i)) x.vector = 0 at h
  rw [pairing_single_right, pairing_single_left, map_mul] at h
  have he : J.conj (x.vector i) * x.vector i = 0 := by
    calc
      _ = (c + J.conj c) * (J.conj (x.vector i) * x.vector i) := by rw [hc, one_mul]
      _ = 0 := by linear_combination h
  rcases mul_eq_zero.mp he with hi | hi
  · exact J.conj.injective (by simpa using hi)
  · exact hi

/-- Every central element is one commutator. -/
theorem exists_commutator_of_vector_eq_zero (c : F) (hc : c + J.conj c = 1)
    (x : Coord J) (hx : x.vector = 0) : ∃ a b : Coord J, ⁅a, b⁆ = x := by
  have hs : J.conj x.scalar = x.scalar := by
    have h := x.trace_eq
    rw [hx, pairing_zero_left] at h
    exact add_left_cancel (h.trans (CharTwo.add_self_eq_zero x.scalar).symm)
  refine ⟨liftVector c hc (Pi.single 0 1),
    liftVector c hc (Pi.single 0 (c * x.scalar)), ?_⟩
  apply Coord.ext
  · rw [commutator_vector, hx]
  · rw [commutator_scalar]
    simp only [liftVector_vector, pairing_single_right,
      Pi.single_eq_same, map_one, one_mul, mul_one, map_mul, hs]
    rw [← add_mul, hc, one_mul]

theorem commutator_eq_center (c : F) (hc : c + J.conj c = 1) :
    commutator (Coord J) = Subgroup.center (Coord J) := by
  apply le_antisymm
  · rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    exact mem_center_of_vector_eq_zero _ (commutator_vector x y)
  · intro x hx
    obtain ⟨a, b, rfl⟩ := exists_commutator_of_vector_eq_zero c hc x
      ((mem_center_iff_vector_eq_zero c hc x).mp hx)
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)


instance [Finite F] : Finite (Coord J) :=
  Finite.of_injective (fun x : Coord J => (x.vector, x.scalar)) (by
    intro x y h
    exact Coord.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

theorem frattini_eq_center [Finite F] (c : F) (hc : c + J.conj c = 1) :
    frattini (Coord J) = Subgroup.center (Coord J) := by
  rw [isPGroup.frattini_eq_closure_squares]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    exact mem_center_of_vector_eq_zero _ (square_vector x)
  · rw [← commutator_eq_center c hc]
    exact commutator_le_closure_squares

/-- Coordinates split as a vector and a fixed-field scalar as sets, not as groups. -/
def paramEquiv (c : F) (hc : c + J.conj c = 1) :
    Coord J ≃ ((Fin 3 → F) × {z : F // J.conj z = z}) where
  toFun x := (x.vector, ⟨x.scalar + c * pairing J x.vector x.vector, by
    rw [map_add, map_mul, conj_pairing]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination x.trace_eq + pairing J x.vector x.vector * hc -
      (x.scalar + c * pairing J x.vector x.vector - pairing J x.vector x.vector) * h2⟩)
  invFun x := ⟨x.1, x.2.val + c * pairing J x.1 x.1, by
    rw [map_add, map_mul, x.2.property, conj_pairing]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination pairing J x.1 x.1 * hc + x.2.val * h2⟩
  left_inv x := by
    apply Coord.ext
    · rfl
    dsimp
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  right_inv x := by
    apply Prod.ext
    · rfl
    apply Subtype.ext
    dsimp
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

theorem card [Finite F] (c : F) (hc : c + J.conj c = 1) :
    Nat.card (Coord J) = Nat.card F ^ 3 * Nat.card {z : F // J.conj z = z} := by
  rw [Nat.card_congr (paramEquiv c hc), Nat.card_prod, Nat.card_fun, Nat.card_fin]

/-- The scalar coordinate parametrizes the center by the fixed field. -/
def centerEquiv (c : F) (hc : c + J.conj c = 1) :
    Subgroup.center (Coord J) ≃ {z : F // J.conj z = z} where
  toFun x := ⟨x.val.scalar, by
    have h := x.val.trace_eq
    rw [(mem_center_iff_vector_eq_zero c hc x.val).mp x.property, pairing_zero_left] at h
    exact add_left_cancel (h.trans (CharTwo.add_self_eq_zero x.val.scalar).symm)⟩
  invFun z := ⟨⟨0, z.val, by simp [z.property, CharTwo.add_self_eq_zero]⟩,
    mem_center_of_vector_eq_zero _ rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Coord.ext
    · exact ((mem_center_iff_vector_eq_zero c hc x.val).mp x.property).symm
    · rfl
  right_inv _ := rfl

theorem card_center (c : F) (hc : c + J.conj c = 1) :
    Nat.card (Subgroup.center (Coord J)) = Nat.card {z : F // J.conj z = z} :=
  Nat.card_congr (centerEquiv c hc)


/-- An isometry of the middle Hermitian space acts on the radical coordinates. -/
def isometryAut (A : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
    (hA : ∀ v w, pairing J (A v) (A w) = pairing J v w) : MulAut (Coord J) where
  toFun x := ⟨A x.vector, x.scalar, by rw [hA]; exact x.trace_eq⟩
  invFun x := ⟨A.symm x.vector, x.scalar, by
    rw [← hA, A.apply_symm_apply]; exact x.trace_eq⟩
  left_inv x := by apply Coord.ext <;> simp
  right_inv x := by apply Coord.ext <;> simp
  map_mul' x y := by
    apply Coord.ext
    · exact A.map_add _ _
    · dsimp
      rw [hA]

end Coord

/-- A nontrivial field involution in characteristic two admits a trace-one scalar. -/
theorem exists_trace_one (hne : ∃ b : F, J.conj b ≠ b) :
    ∃ c : F, c + J.conj c = 1 := by
  obtain ⟨b, hb⟩ := hne
  have hd : b + J.conj b ≠ 0 := by
    intro h
    exact hb (add_left_cancel (h.trans (CharTwo.add_self_eq_zero b).symm))
  refine ⟨b / (b + J.conj b), ?_⟩
  rw [map_div₀, map_add, J.conj_involutive, add_comm (J.conj b) b,
    ← add_div, div_self hd]

end Theory.SpecificGroups.UnitaryFive.LineCore
