module

public import Theory.Representation.BinaryPermutationAlternatingActions
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.Abel

/-!
# Coordinate group of even signed six-letter monomials

An element is a binary sign and an even-weight binary six-vector. The
upper-triangular bilinear cocycle counts the sign introduced by collecting
monomials in increasing letter order. Bilinearity proves associativity; the
square formula gives inverses. Projection to the literal augmentation core
has the central order-two sign kernel. The volume element has order four.

These are intrinsic definitions, independent of a covering group. They supply
the coordinate group and quotient maps for the quartic radical in
Aschbacher–Smith, combined manuscript (1 March 2004), I.2.2(6), printed pp.410
and 412. The signed action and central-product recognition are separate proofs.
-/

@[expose] public section

namespace EvenCliffordSix
open BinaryPermutation

abbrev F := ZMod 2
abbrev V := core (Fin 6)
abbrev A := alternatingGroup (Fin 6)

/-- The upper-triangular binary cocycle. -/
def cocycle (v w : Fin 6 → F) : F :=
  ∑ i, (∑ j ∈ Finset.Ioi i, v j * w i)

@[simp] theorem cocycle_zero_left (v : Fin 6 → F) : cocycle 0 v = 0 := by
  simp [cocycle]

@[simp] theorem cocycle_zero_right (v : Fin 6 → F) : cocycle v 0 = 0 := by
  simp [cocycle]

theorem cocycle_add_left (u v w : Fin 6 → F) :
    cocycle (u + v) w = cocycle u w + cocycle v w := by
  simp only [cocycle, Pi.add_apply, add_mul]
  simp_rw [Finset.sum_add_distrib]

theorem cocycle_add_right (u v w : Fin 6 → F) :
    cocycle u (v + w) = cocycle u v + cocycle u w := by
  simp only [cocycle, Pi.add_apply, mul_add]
  simp_rw [Finset.sum_add_distrib]

/-- Coordinate pairs for the quartic radical. -/
@[ext] structure Model where
  sign : F
  vector : V
  deriving DecidableEq

instance : One Model := ⟨⟨0, 0⟩⟩

instance : Mul Model := ⟨fun x y =>
  ⟨x.sign + y.sign + cocycle x.vector.val y.vector.val, x.vector + y.vector⟩⟩

instance : Inv Model := ⟨fun x =>
  ⟨x.sign + cocycle x.vector.val x.vector.val, x.vector⟩⟩

instance : DecidablePred (fun v : Full (Fin 6) => v ∈ core (Fin 6)) :=
  fun v => decidable_of_iff (∑ i, v i = 0) Iff.rfl

instance : Fintype V := Subtype.fintype _

instance : Group Model where
  mul_assoc x y z := by
    apply Model.ext
    · change (x.sign + y.sign + cocycle x.vector.val y.vector.val) + z.sign +
        cocycle (x.vector.val + y.vector.val) z.vector.val =
        x.sign + (y.sign + z.sign + cocycle y.vector.val z.vector.val) +
        cocycle x.vector.val (y.vector.val + z.vector.val)
      rw [cocycle_add_left, cocycle_add_right]
      abel
    · exact add_assoc _ _ _
  one_mul x := by
    apply Model.ext
    · change 0 + x.sign + cocycle 0 x.vector.val = x.sign
      simp
    · exact zero_add _
  mul_one x := by
    apply Model.ext
    · change x.sign + 0 + cocycle x.vector.val 0 = x.sign
      simp
    · exact add_zero _
  inv_mul_cancel x := by
    apply Model.ext
    · change (x.sign + cocycle x.vector.val x.vector.val) + x.sign +
        cocycle x.vector.val x.vector.val = 0
      calc
        (x.sign + cocycle x.vector.val x.vector.val) + x.sign +
            cocycle x.vector.val x.vector.val =
            (x.sign + x.sign) +
              (cocycle x.vector.val x.vector.val + cocycle x.vector.val x.vector.val) := by abel
        _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add]
    · apply Subtype.ext
      ext i
      exact CharTwo.add_self_eq_zero _

/-- The coordinate equivalence makes finiteness of the model computational. -/
def coordinates : Model ≃ F × V where
  toFun x := (x.sign, x.vector)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Model := Fintype.ofEquiv (F × V) coordinates.symm

@[simp] theorem card : Nat.card Model = 64 := by
  rw [Nat.card_congr coordinates, Nat.card_prod,
    Module.natCard_eq_pow_finrank (K := F) (V := V), finrank_core]
  norm_num [F]

/-- Projection onto the even permutation module. -/
def projection : Model →* Multiplicative V where
  toFun x := Multiplicative.ofAdd x.vector
  map_one' := rfl
  map_mul' _ _ := rfl

theorem projection_surjective : Function.Surjective projection :=
  fun v => ⟨⟨0, v.toAdd⟩, rfl⟩

/-- The central sign and the volume element. -/
def centralSign (a : F) : Model := ⟨a, 0⟩
def involution : Model := centralSign 1
def volumeVector : V := ⟨![1, 1, 1, 1, 1, 1], by rw [mem_core]; decide⟩
def volume : Model := ⟨0, volumeVector⟩

theorem volume_sq : volume ^ 2 = involution := by
  rw [pow_two]
  apply Model.ext
  · change (0 : F) + 0 + cocycle volumeVector.val volumeVector.val = 1
    norm_num [cocycle, volumeVector, Fin.sum_univ_succ]
    decide
  · apply Subtype.ext
    funext i
    change volumeVector.val i + volumeVector.val i = 0
    exact CharTwo.add_self_eq_zero _

theorem involution_ne_one : involution ≠ 1 := by decide

theorem involution_sq : involution ^ 2 = 1 := by
  apply Model.ext
  · change (1 : F) + 1 = 0
    exact CharTwo.add_self_eq_zero _
  · rfl


@[simp] theorem mul_sign (x y : Model) :
    (x * y).sign = x.sign + y.sign + cocycle x.vector.val y.vector.val := rfl

@[simp] theorem mul_vector (x y : Model) : (x * y).vector = x.vector + y.vector := rfl

@[simp] theorem one_sign : (1 : Model).sign = 0 := rfl
@[simp] theorem one_vector : (1 : Model).vector = 0 := rfl
@[simp] theorem inv_vector (x : Model) : x⁻¹.vector = x.vector := rfl

@[simp] theorem projection_apply (x : Model) : (projection x).toAdd = x.vector := rfl

/-- The central sign inclusion, with its specified generator. -/
def signEmbedding : Multiplicative F →* Model where
  toFun a := centralSign a.toAdd
  map_one' := rfl
  map_mul' a b := by
    apply Model.ext
    · change a.toAdd + b.toAdd = a.toAdd + b.toAdd + cocycle 0 0
      simp
    · exact (zero_add _).symm

theorem signEmbedding_injective : Function.Injective signEmbedding :=
  fun _ _ h => Multiplicative.toAdd.injective (congrArg Model.sign h)

@[simp] theorem centralSign_mul (a : F) (x : Model) :
    centralSign a * x = ⟨a + x.sign, x.vector⟩ := by
  apply Model.ext
  · change a + x.sign + cocycle 0 x.vector.val = a + x.sign
    simp
  · exact zero_add _

@[simp] theorem mul_centralSign (x : Model) (a : F) :
    x * centralSign a = ⟨x.sign + a, x.vector⟩ := by
  apply Model.ext
  · change x.sign + a + cocycle x.vector.val 0 = x.sign + a
    simp
  · exact add_zero _

theorem centralSign_mem_center (a : F) : centralSign a ∈ Subgroup.center Model := by
  rw [Subgroup.mem_center_iff]
  intro x
  rw [centralSign_mul, mul_centralSign, add_comm]

/-- The literal kernel of the augmentation projection. -/
def signKernel : Subgroup Model := projection.ker

instance : signKernel.Normal := inferInstanceAs projection.ker.Normal

@[simp] theorem mem_signKernel (x : Model) : x ∈ signKernel ↔ x.vector = 0 := Iff.rfl

theorem signKernel_eq_range : signKernel = signEmbedding.range := by
  ext x
  constructor
  · intro hx
    exact ⟨Multiplicative.ofAdd x.sign, Model.ext rfl hx.symm⟩
  · rintro ⟨a, rfl⟩
    rfl

theorem signKernel_le_center : signKernel ≤ Subgroup.center Model := by
  rw [signKernel_eq_range]
  rintro _ ⟨a, rfl⟩
  exact centralSign_mem_center a.toAdd

/-- The two elements in the projection kernel, explicitly. -/
theorem mem_signKernel_iff (x : Model) :
    x ∈ signKernel ↔ x = 1 ∨ x = involution := by
  rw [mem_signKernel]
  constructor
  · intro h
    have hc : ∀ a : F, a = 0 ∨ a = 1 := by decide
    rcases hc x.sign with hs | hs
    · exact Or.inl (Model.ext hs h)
    · exact Or.inr (Model.ext hs h)
  · rintro (rfl | rfl) <;> rfl

theorem signKernel_eq_zpowers : signKernel = Subgroup.zpowers involution := by
  apply le_antisymm
  · intro x hx
    rcases (mem_signKernel_iff x).mp hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr rfl

/-- Squaring loses the vector coordinate and records the cocycle diagonal. -/
theorem square (x : Model) : x ^ 2 = centralSign (cocycle x.vector.val x.vector.val) := by
  rw [pow_two]
  apply Model.ext
  · change x.sign + x.sign + cocycle x.vector.val x.vector.val = _
    rw [CharTwo.add_self_eq_zero, zero_add]
    rfl
  · apply Subtype.ext
    funext i
    exact CharTwo.add_self_eq_zero _

theorem involution_order : orderOf involution = 2 :=
  orderOf_eq_prime involution_sq involution_ne_one

theorem volume_order : orderOf volume = 4 := by
  have hfour : volume ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, volume_sq, involution_sq]
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) hfour
  intro p hp hd
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 from hd))
  subst p
  simpa only [Nat.reduceDiv, volume_sq] using involution_ne_one

theorem signKernel_card : Nat.card signKernel = 2 := by
  rw [signKernel_eq_zpowers, Nat.card_zpowers, involution_order]

/-- The first isomorphism theorem, preserving the original coordinate map. -/
noncomputable def quotientEquiv :
    (Model ⧸ signKernel) ≃* Multiplicative V :=
  QuotientGroup.quotientKerEquivOfSurjective projection projection_surjective

@[simp] theorem quotientEquiv_mk (x : Model) :
    quotientEquiv (QuotientGroup.mk' signKernel x) = Multiplicative.ofAdd x.vector := rfl

/-- Reordering sign on increasing pairs. No ambient radical is used. -/
def signedCorrection (p : Equiv.Perm (Fin 6)) (v : V) : F :=
  ∑ i, ∑ j, if i < j ∧ p j < p i then v.val i * v.val j else 0

/-- Coordinate permutation with the literal left-action convention. -/
def permuteVector (p : Equiv.Perm (Fin 6)) (v : V) : V :=
  ⟨fun i => v.val (p.symm i), core_invariant (Fin 6) p v.property⟩

@[simp] theorem permuteVector_eq (p : Equiv.Perm (Fin 6)) (v : V) :
    permuteVector p v = coreRepresentation (Fin 6) p v := rfl

/-- Candidate signed permutation formula, to be proved an action in the
signed-action extension. -/
def signedTo (p : Equiv.Perm (Fin 6)) (x : Model) : Model :=
  ⟨x.sign + signedCorrection p x.vector, permuteVector p x.vector⟩

@[simp] theorem signedTo_projection (p : Equiv.Perm (Fin 6)) (x : Model) :
    projection (signedTo p x) =
      Multiplicative.ofAdd (coreRepresentation (Fin 6) p x.vector) := rfl

end EvenCliffordSix
