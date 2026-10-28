module

public import Theory.SpecificGroups.MacWilliams.SylowPresentations
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Involutions in the unitary MacWilliams Sylow presentation

The presentation in `SylowPresentations` has exactly 64 elements and three
involutions. Its normal forms are ordered words with six binary exponents.
The last two coordinates are central; multiplication adds a lower triangular
bilinear cocycle determined by the given squares and commutators.

We construct this finite coordinate group and check the presentation relations.
Collection inside the presented group proves that all elements have one of the
64 normal forms. Interpretation in the coordinate group distinguishes those
forms, so the two groups are isomorphic. Kernel-checked finite enumeration of
the quadratic square equation then gives the involution count. No group order,
rank, recognition theorem, or external computation is assumed.

Source: the MacWilliams alternative cited in Janko–Thompson, Math. Z. 113
(1970), Theorem 1.3, p.386, and Lemma 5.1, p.393. The exact presentation and
commutator convention are those of `SylowPresentations`.
-/

namespace MacWilliamsSylow.UnitaryCoordinates

/-- Binary exponents in the ordered word in the six generators. -/
structure C where
  a : Bool
  b : Bool
  c : Bool
  d : Bool
  e : Bool
  f : Bool
  deriving DecidableEq, Fintype

/-- The lower triangular bilinear cocycle prescribed by the square and
commutator table; the last two coordinates are central. -/
def op (x y : C) : C :=
  ⟨x.a ^^ y.a, x.b ^^ y.b, x.c ^^ y.c, x.d ^^ y.d,
    x.e ^^ y.e ^^ (x.a && y.a) ^^ (x.d && y.d) ^^ (x.b && y.a) ^^
      (x.d && y.a) ^^ (x.c && y.b) ^^ (x.d && y.b),
    x.f ^^ y.f ^^ (x.b && y.b) ^^ (x.c && y.c) ^^ (x.c && y.a) ^^
      (x.d && y.a) ^^ (x.c && y.b)⟩

def id : C := ⟨false, false, false, false, false, false⟩

def inv (x : C) : C :=
  ⟨x.a, x.b, x.c, x.d, (op x x).e ^^ x.e, (op x x).f ^^ x.f⟩

@[ext] theorem ext {x y : C} (ha : x.a = y.a) (hb : x.b = y.b)
    (hc : x.c = y.c) (hd : x.d = y.d) (he : x.e = y.e) (hf : x.f = y.f) : x = y := by
  cases x; cases y; simp_all

local instance : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩
local instance : Std.Associative Bool.xor := ⟨Bool.xor_assoc⟩

instance : Group C where
  mul := op
  one := id
  inv := inv
  mul_assoc x y z := by
    change op (op x y) z = op x (op y z)
    ext <;> simp only [op, Bool.and_xor_distrib_left, Bool.and_xor_distrib_right] <;>
      ac_rfl
  one_mul x := by
    change op id x = x
    ext <;> simp [op, id]
  mul_one x := by
    change op x id = x
    ext <;> simp [op, id]
  inv_mul_cancel x := by
    rcases x with ⟨a, b, c, d, e, f⟩
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

def basis : Fin 6 → C
  | 0 => ⟨true, false, false, false, false, false⟩
  | 1 => ⟨false, true, false, false, false, false⟩
  | 2 => ⟨false, false, true, false, false, false⟩
  | 3 => ⟨false, false, false, true, false, false⟩
  | 4 => ⟨false, false, false, false, true, false⟩
  | 5 => ⟨false, false, false, false, false, true⟩

theorem relations : Relations unitaryTable basis where
  square := by decide
  commutator := by decide

def eval {G : Type*} [Group G] (g : Fin 6 → G) (x : C) : G :=
  (if x.a then g 0 else 1) * (if x.b then g 1 else 1) *
    (if x.c then g 2 else 1) * (if x.d then g 3 else 1) *
    (if x.e then g 4 else 1) * (if x.f then g 5 else 1)

set_option maxRecDepth 4096 in
theorem eval_basis : ∀ x, eval basis x = x := by decide

abbrev g := generator unitaryTable

theorem sq_rule (i : Fin 6) : g i * g i = word g (unitaryTable.square i) :=
  (generator_relations unitaryTable).square i

theorem comm_rule (i j : Fin 6) (h : i < j) :
    g j * g i = g i * g j * word g (unitaryTable.commutator j i) := by
  rw [← (generator_relations unitaryTable).commutator i j h]
  simp [rightComm, mul_assoc]

theorem square_0 : g 0 * g 0 = g 4 := by
  have h := sq_rule 0
  change g 0 * g 0 = g 4 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem square_0_assoc (x : UnitarySylow) : g 0 * (g 0 * x) = g 4 * x := by
  rw [← mul_assoc, square_0]

theorem swap_10 : g 1 * g 0 = g 0 * g 1 * g 4 := by
  have h := comm_rule 0 1 (by decide)
  change g 1 * g 0 = g 0 * g 1 * (g 4 * 1) at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_10_assoc (x : UnitarySylow) : g 1 * (g 0 * x) = (g 0 * g 1 * g 4) * x := by
  rw [← mul_assoc, swap_10]

theorem square_1 : g 1 * g 1 = g 5 := by
  have h := sq_rule 1
  change g 1 * g 1 = g 5 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem square_1_assoc (x : UnitarySylow) : g 1 * (g 1 * x) = g 5 * x := by
  rw [← mul_assoc, square_1]

theorem swap_20 : g 2 * g 0 = g 0 * g 2 * g 5 := by
  have h := comm_rule 0 2 (by decide)
  change g 2 * g 0 = g 0 * g 2 * (g 5 * 1) at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_20_assoc (x : UnitarySylow) : g 2 * (g 0 * x) = (g 0 * g 2 * g 5) * x := by
  rw [← mul_assoc, swap_20]

theorem swap_21 : g 2 * g 1 = g 1 * g 2 * g 4 * g 5 := by
  have h := comm_rule 1 2 (by decide)
  change g 2 * g 1 = g 1 * g 2 * (g 4 * (g 5 * 1)) at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_21_assoc (x : UnitarySylow) : g 2 * (g 1 * x) = (g 1 * g 2 * g 4 * g 5) * x := by
  rw [← mul_assoc, swap_21]

theorem square_2 : g 2 * g 2 = g 5 := by
  have h := sq_rule 2
  change g 2 * g 2 = g 5 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem square_2_assoc (x : UnitarySylow) : g 2 * (g 2 * x) = g 5 * x := by
  rw [← mul_assoc, square_2]

theorem swap_30 : g 3 * g 0 = g 0 * g 3 * g 4 * g 5 := by
  have h := comm_rule 0 3 (by decide)
  change g 3 * g 0 = g 0 * g 3 * (g 4 * (g 5 * 1)) at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_30_assoc (x : UnitarySylow) : g 3 * (g 0 * x) = (g 0 * g 3 * g 4 * g 5) * x := by
  rw [← mul_assoc, swap_30]

theorem swap_31 : g 3 * g 1 = g 1 * g 3 * g 4 := by
  have h := comm_rule 1 3 (by decide)
  change g 3 * g 1 = g 1 * g 3 * (g 4 * 1) at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_31_assoc (x : UnitarySylow) : g 3 * (g 1 * x) = (g 1 * g 3 * g 4) * x := by
  rw [← mul_assoc, swap_31]

theorem swap_32 : g 3 * g 2 = g 2 * g 3 := by
  have h := comm_rule 2 3 (by decide)
  change g 3 * g 2 = g 2 * g 3 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_32_assoc (x : UnitarySylow) : g 3 * (g 2 * x) = (g 2 * g 3) * x := by
  rw [← mul_assoc, swap_32]

theorem square_3 : g 3 * g 3 = g 4 := by
  have h := sq_rule 3
  change g 3 * g 3 = g 4 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem square_3_assoc (x : UnitarySylow) : g 3 * (g 3 * x) = g 4 * x := by
  rw [← mul_assoc, square_3]

theorem swap_40 : g 4 * g 0 = g 0 * g 4 := by
  have h := comm_rule 0 4 (by decide)
  change g 4 * g 0 = g 0 * g 4 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_40_assoc (x : UnitarySylow) : g 4 * (g 0 * x) = (g 0 * g 4) * x := by
  rw [← mul_assoc, swap_40]

theorem swap_41 : g 4 * g 1 = g 1 * g 4 := by
  have h := comm_rule 1 4 (by decide)
  change g 4 * g 1 = g 1 * g 4 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_41_assoc (x : UnitarySylow) : g 4 * (g 1 * x) = (g 1 * g 4) * x := by
  rw [← mul_assoc, swap_41]

theorem swap_42 : g 4 * g 2 = g 2 * g 4 := by
  have h := comm_rule 2 4 (by decide)
  change g 4 * g 2 = g 2 * g 4 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_42_assoc (x : UnitarySylow) : g 4 * (g 2 * x) = (g 2 * g 4) * x := by
  rw [← mul_assoc, swap_42]

theorem swap_43 : g 4 * g 3 = g 3 * g 4 := by
  have h := comm_rule 3 4 (by decide)
  change g 4 * g 3 = g 3 * g 4 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_43_assoc (x : UnitarySylow) : g 4 * (g 3 * x) = (g 3 * g 4) * x := by
  rw [← mul_assoc, swap_43]

theorem square_4 : g 4 * g 4 = 1 := by
  have h := sq_rule 4
  change g 4 * g 4 = 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem square_4_assoc (x : UnitarySylow) : g 4 * (g 4 * x) = 1 * x := by
  rw [← mul_assoc, square_4]

theorem swap_50 : g 5 * g 0 = g 0 * g 5 := by
  have h := comm_rule 0 5 (by decide)
  change g 5 * g 0 = g 0 * g 5 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_51 : g 5 * g 1 = g 1 * g 5 := by
  have h := comm_rule 1 5 (by decide)
  change g 5 * g 1 = g 1 * g 5 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_52 : g 5 * g 2 = g 2 * g 5 := by
  have h := comm_rule 2 5 (by decide)
  change g 5 * g 2 = g 2 * g 5 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_52_assoc (x : UnitarySylow) : g 5 * (g 2 * x) = (g 2 * g 5) * x := by
  rw [← mul_assoc, swap_52]

theorem swap_53 : g 5 * g 3 = g 3 * g 5 := by
  have h := comm_rule 3 5 (by decide)
  change g 5 * g 3 = g 3 * g 5 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_53_assoc (x : UnitarySylow) : g 5 * (g 3 * x) = (g 3 * g 5) * x := by
  rw [← mul_assoc, swap_53]

theorem swap_54 : g 5 * g 4 = g 4 * g 5 := by
  have h := comm_rule 4 5 (by decide)
  change g 5 * g 4 = g 4 * g 5 * 1 at h
  simpa only [mul_one, mul_assoc] using h

theorem swap_54_assoc (x : UnitarySylow) : g 5 * (g 4 * x) = (g 4 * g 5) * x := by
  rw [← mul_assoc, swap_54]

theorem square_5 : g 5 * g 5 = 1 := by
  have h := sq_rule 5
  change g 5 * g 5 = 1 at h
  simpa only [mul_one, mul_assoc] using h

set_option maxHeartbeats 4000000 in
/-- Collection after multiplication by a generator, checked for every binary
word using only the defining equations in the presented group. -/
theorem eval_step (x : C) (i : Fin 6) : eval g x * g i = eval g (x * basis i) := by
  change eval g x * g i = eval g (op x (basis i))
  rcases x with ⟨a, b, c, d, e, f⟩
  fin_cases i <;>
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
    simp only [Fin.reduceFinMk, Bool.xor, Bool.and, eval, basis, op, Bool.false_eq_true,
      ↓reduceIte, mul_assoc, one_mul, mul_one, square_0, square_0_assoc, swap_10, swap_10_assoc,
      square_1, square_1_assoc, swap_20, swap_20_assoc, swap_21, swap_21_assoc, square_2,
      square_2_assoc, swap_30, swap_30_assoc, swap_31, swap_31_assoc, swap_32, swap_32_assoc,
      square_3, square_3_assoc, swap_40, swap_40_assoc, swap_41, swap_41_assoc, swap_42,
      swap_42_assoc, swap_43, swap_43_assoc, square_4, square_4_assoc, swap_50, swap_51, swap_52,
      swap_52_assoc, swap_53, swap_53_assoc, swap_54, swap_54_assoc, square_5] <;> rfl

/-- Collection covers the presentation, including words with inverse letters. -/
theorem eval_surjective : Function.Surjective (eval g) := by
  intro y
  have hy : y ∈ Subgroup.closure (Set.range g) := by
    rw [generator_closure]; trivial
  induction hy using Subgroup.closure_induction_right with
  | one => exact ⟨1, rfl⟩
  | mul_right y _ z hz ih =>
    obtain ⟨i, rfl⟩ := hz
    obtain ⟨x, rfl⟩ := ih
    exact ⟨x * basis i, (eval_step x i).symm⟩
  | mul_inv_cancel y _ z hz ih =>
    obtain ⟨i, rfl⟩ := hz
    obtain ⟨x, rfl⟩ := ih
    refine ⟨x * (basis i)⁻¹, ?_⟩
    apply (eq_mul_inv_iff_mul_eq).mpr
    rw [eval_step, inv_mul_cancel_right]

def interpretation : UnitarySylow →* C := presentationHom relations

theorem interpretation_eval (x : C) : interpretation (eval g x) = x := by
  calc
    interpretation (eval g x) = eval basis x := by
      have hm (b : Bool) (i : Fin 6) :
          interpretation (if b then g i else 1) = if b then basis i else 1 := by
        cases b <;> simp [interpretation, g]
      simp only [eval, map_mul, hm]
    _ = x := eval_basis x

/-- The finite model distinguishes all collected words. -/
theorem interpretation_bijective : Function.Bijective interpretation := by
  constructor
  · intro y z h
    obtain ⟨x, rfl⟩ := eval_surjective y
    obtain ⟨w, rfl⟩ := eval_surjective z
    rw [interpretation_eval, interpretation_eval] at h
    rw [h]
  · intro x
    exact ⟨eval g x, interpretation_eval x⟩

noncomputable def equivalence : UnitarySylow ≃* C :=
  MulEquiv.ofBijective interpretation interpretation_bijective

/-- Kernel-checked enumeration of the nonidentity solutions to the quadratic
square equation in the six binary coordinates. -/
theorem coordinate_count : Nat.card {x : C // x * x = 1 ∧ x ≠ 1} = 3 := by
  rw [Nat.card_eq_fintype_card]
  decide

end MacWilliamsSylow.UnitaryCoordinates

namespace MacWilliamsSylow

/-- The six-generator unitary Sylow presentation is finite. -/
public instance unitarySylowFinite : Finite UnitarySylow :=
  Finite.of_surjective _ UnitaryCoordinates.eval_surjective

/-- The ordered binary words are the 64 distinct elements of the presentation. -/
public theorem unitarySylow_card : Nat.card UnitarySylow = 64 := by
  rw [Nat.card_congr UnitaryCoordinates.equivalence.toEquiv,
    Nat.card_eq_fintype_card]
  decide

/-- The unitary Sylow presentation has exactly three involutions. -/
public theorem unitarySylow_involution_count :
    Nat.card {x : UnitarySylow // orderOf x = 2} = 3 := by
  let e := UnitaryCoordinates.equivalence
  let e' := e.toEquiv.subtypeEquiv (p := fun x => orderOf x = 2)
    (q := fun x => x * x = 1 ∧ x ≠ 1) (fun x => by
      change orderOf x = 2 ↔ e x * e x = 1 ∧ e x ≠ 1
      rw [← e.orderOf_eq x, orderOf_eq_prime_iff, pow_two])
  exact (Nat.card_congr e').trans UnitaryCoordinates.coordinate_count

end MacWilliamsSylow
