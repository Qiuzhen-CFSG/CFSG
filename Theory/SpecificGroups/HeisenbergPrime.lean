module
public import Theory.ElementaryAbelian.Extraspecial
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The prime Heisenberg group

The carrier consists of triples over `ZMod p`, with multiplication
`(a,b,c)(x,y,z) = (a+x,b+y,c+z+a*y)`. For odd primes it has exponent p,
order p³, and center the third coordinate line. This is the concrete
extraspecial model denoted p^(1+2) in Aschbacher–Smith, Notation A.1.22.
-/

@[ext] public structure HeisenbergPrime (p : ℕ) where
  a : ZMod p
  b : ZMod p
  c : ZMod p

namespace HeisenbergPrime

variable {p : ℕ}

public instance : Mul (HeisenbergPrime p) where
  mul s t := ⟨s.a + t.a, s.b + t.b, s.c + t.c + s.a * t.b⟩

public instance : One (HeisenbergPrime p) where
  one := ⟨0, 0, 0⟩

public instance : Inv (HeisenbergPrime p) where
  inv s := ⟨-s.a, -s.b, -s.c + s.a * s.b⟩

public instance : Group (HeisenbergPrime p) where
  mul_assoc s t u := by
    apply HeisenbergPrime.ext
    · exact add_assoc s.a t.a u.a
    · exact add_assoc s.b t.b u.b
    · change (s.c + t.c + s.a * t.b) + u.c + (s.a + t.a) * u.b =
        s.c + (t.c + u.c + t.a * u.b) + s.a * (t.b + u.b)
      ring
  one_mul s := by
    apply HeisenbergPrime.ext
    · exact zero_add s.a
    · exact zero_add s.b
    · change 0 + s.c + 0 * s.b = s.c
      ring
  mul_one s := by
    apply HeisenbergPrime.ext
    · exact add_zero s.a
    · exact add_zero s.b
    · change s.c + 0 + s.a * 0 = s.c
      ring
  inv_mul_cancel s := by
    apply HeisenbergPrime.ext
    · exact neg_add_cancel s.a
    · exact neg_add_cancel s.b
    · change (-s.c + s.a * s.b) + s.c + (-s.a) * s.b = 0
      ring

@[expose] public def coordinatesEquiv : HeisenbergPrime p ≃ ZMod p × ZMod p × ZMod p where
  toFun s := (s.a, s.b, s.c)
  invFun s := ⟨s.1, s.2.1, s.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

public instance [NeZero p] : Fintype (HeisenbergPrime p) :=
  Fintype.ofEquiv _ coordinatesEquiv.symm

public theorem card [NeZero p] : Nat.card (HeisenbergPrime p) = p ^ 3 := by
  rw [Nat.card_congr coordinatesEquiv, Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  ring

@[simp] public theorem mul_a (s t : HeisenbergPrime p) : (s * t).a = s.a + t.a := rfl
@[simp] public theorem mul_b (s t : HeisenbergPrime p) : (s * t).b = s.b + t.b := rfl
@[simp] public theorem mul_c (s t : HeisenbergPrime p) : (s * t).c = s.c + t.c + s.a * t.b := rfl
@[simp] public theorem one_a : (1 : HeisenbergPrime p).a = 0 := rfl
@[simp] public theorem one_b : (1 : HeisenbergPrime p).b = 0 := rfl
@[simp] public theorem one_c : (1 : HeisenbergPrime p).c = 0 := rfl
@[simp] public theorem inv_a (s : HeisenbergPrime p) : s⁻¹.a = -s.a := rfl
@[simp] public theorem inv_b (s : HeisenbergPrime p) : s⁻¹.b = -s.b := rfl
@[simp] public theorem inv_c (s : HeisenbergPrime p) : s⁻¹.c = -s.c + s.a * s.b := rfl

public theorem mem_center_iff (s : HeisenbergPrime p) :
    s ∈ Subgroup.center (HeisenbergPrime p) ↔ s.a = 0 ∧ s.b = 0 := by
  constructor
  · intro h
    have h₁ := congrArg HeisenbergPrime.c
      (Subgroup.mem_center_iff.mp h (⟨0, 1, 0⟩ : HeisenbergPrime p))
    have h₂ := congrArg HeisenbergPrime.c
      (Subgroup.mem_center_iff.mp h (⟨1, 0, 0⟩ : HeisenbergPrime p))
    constructor
    · simpa using h₁.symm
    · simpa using h₂
  · rintro ⟨ha, hb⟩
    apply Subgroup.mem_center_iff.mpr
    intro t
    ext <;> simp [ha, hb, add_comm]

@[expose] public def centerEquiv :
    Subgroup.center (HeisenbergPrime p) ≃* Multiplicative (ZMod p) where
  toFun s := Multiplicative.ofAdd s.val.c
  invFun z := ⟨⟨0, 0, Multiplicative.toAdd z⟩, (mem_center_iff _).mpr ⟨rfl, rfl⟩⟩
  left_inv s := by
    apply Subtype.ext
    obtain ⟨ha, hb⟩ := (mem_center_iff s.val).mp s.property
    ext <;> simp [ha, hb]
  right_inv _ := rfl
  map_mul' s t := by
    change s.val.c + t.val.c + s.val.a * t.val.b = s.val.c + t.val.c
    rw [((mem_center_iff s.val).mp s.property).1, zero_mul, add_zero]

public theorem card_center [NeZero p] : Nat.card (Subgroup.center (HeisenbergPrime p)) = p := by
  rw [Nat.card_congr centerEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

open scoped commutatorElement

public theorem commutator_coordinates (s t : HeisenbergPrime p) :
    ⁅s, t⁆ = ⟨0, 0, s.a * t.b - t.a * s.b⟩ := by
  ext <;> simp only [commutatorElement_def, mul_a, mul_b, mul_c, inv_a, inv_b, inv_c] <;> ring

public theorem commutator_le_center :
    _root_.commutator (HeisenbergPrime p) ≤ Subgroup.center (HeisenbergPrime p) := by
  apply Subgroup.commutator_le.mpr
  intro s _ t _
  rw [commutator_coordinates]
  exact (mem_center_iff _).mpr ⟨rfl, rfl⟩

public theorem not_isMulCommutative [Fact p.Prime] : ¬ IsMulCommutative (HeisenbergPrime p) := by
  intro h
  have he := congrArg HeisenbergPrime.c
    (@IsMulCommutative.is_comm _ _ h |>.comm
      (⟨1, 0, 0⟩ : HeisenbergPrime p) (⟨0, 1, 0⟩ : HeisenbergPrime p))
  have : (1 : ZMod p) = 0 := by
    simpa only [mul_c, zero_add, add_zero, one_mul, mul_zero] using he
  exact one_ne_zero this

public theorem pow_a (s : HeisenbergPrime p) (n : ℕ) : (s ^ n).a = n * s.a := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, mul_a, ih, Nat.cast_add, Nat.cast_one]; ring

public theorem pow_b (s : HeisenbergPrime p) (n : ℕ) : (s ^ n).b = n * s.b := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, mul_b, ih, Nat.cast_add, Nat.cast_one]; ring

public theorem two_mul_pow_c (s : HeisenbergPrime p) (n : ℕ) :
    2 * (s ^ n).c = 2 * n * s.c + n * (n - 1 : ZMod p) * s.a * s.b := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, mul_c, pow_a, Nat.cast_add, Nat.cast_one]
    calc
      _ = 2 * (s ^ n).c + 2 * s.c + 2 * n * s.a * s.b := by ring
      _ = _ := by rw [ih]; ring

public theorem pow_prime [Fact p.Prime] (hp : p ≠ 2) (s : HeisenbergPrime p) : s ^ p = 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp ((Nat.prime_two.eq_one_or_self_of_dvd p hd).resolve_left
      (Fact.out : p.Prime).ne_one)
  have hc := two_mul_pow_c s p
  simp only [ZMod.natCast_self, mul_zero, zero_mul, add_zero] at hc
  ext
  · simp [pow_a]
  · simp [pow_b]
  · exact (mul_eq_zero.mp hc).resolve_left h2

public theorem exponent [Fact p.Prime] (hp : p ≠ 2) : Monoid.exponent (HeisenbergPrime p) = p := by
  have hd := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (pow_prime hp)
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hd with h | h
  · have hu := Monoid.pow_exponent_eq_one (⟨1, 0, 0⟩ : HeisenbergPrime p)
    rw [h, pow_one] at hu
    exact (one_ne_zero (congrArg HeisenbergPrime.a hu)).elim
  · exact h

public theorem isExtraspecial [Fact p.Prime] (hp : p ≠ 2) : IsExtraspecial p (HeisenbergPrime p) := by
  refine ⟨card_center, ?_, ?_⟩
  · refine {
      toIsMulCommutative :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr commutator_le_center
      exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (HeisenbergPrime p)) q
    rw [← map_pow, pow_prime hp, map_one]
  · exact QuotientGroup.nontrivial_iff.mpr (fun h =>
      not_isMulCommutative (Subgroup.center_eq_top_iff.mp h))

end HeisenbergPrime
