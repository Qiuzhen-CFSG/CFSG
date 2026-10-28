module

public import Theory.AlgebraicGroup.RootSystems.E7RootPairing
public import Mathlib.Tactic

/-!
# Exact coordinates for the E7 adjoint lattice

The 126 doubled integral root coordinates are 62 signed pair vectors
and 64 even half-sign vectors satisfying the E7 orthogonality equation.
Explicit finite witnesses and completeness certificates identify this catalogue
with the literal standard root set. Its ordering matches the exceptional Levi
matrix calculation; the full Cartan-plus-root basis has dimension 133.
Source: the standard E7 root system and Geck's integral construction, GLS3 §2.6.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.SpecificGroups.LieType.SourceLevi.E7.Operators.Coordinates

namespace Data

def column0 : Array ℤ := #[-2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def column1 : Array ℤ := #[2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1]

def column2 : Array ℤ := #[0, 0, -2, -2, 2, 2, -2, -2, 2, 2, -2, -2, 2, 2, -2, -2, 2, 2, -2, -2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def column3 : Array ℤ := #[0, 0, -2, 2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, 2, 2, -2, -2, 2, 2, -2, -2, 2, 2, -2, -2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1]

def column4 : Array ℤ := #[0, 0, 0, 0, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, 2, 2, -2, -2, 2, 2, -2, -2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1]

def column5 : Array ℤ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, -2, -2, 2, 2, -2, -2, 2, 2, 0, 0, 0, 0, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1]

def column6 : Array ℤ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, -2, -2, 2, 2, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1]

def column7 : Array ℤ := #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, 0, 0, 0, 0, -2, 2, -2, 2, 0, 0, 0, 0, -2, 2, -2, 2, -2, 2, -2, 2, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 1, -1]

end Data

def coord (r : Fin 126) (q : Fin 8) : ℤ :=
  ((#[Data.column0, Data.column1, Data.column2, Data.column3, Data.column4, Data.column5, Data.column6, Data.column7] : Array (Array ℤ))[q.val]!)[r.val]!

private def sign (a : Bool) : ℤ := if a then 1 else -1
private def pair (i j : Fin 8) (a b : Bool) : Fin 8 → ℤ :=
  fun k => (if k = i then 2 * sign a else 0) + (if k = j then 2 * sign b else 0)
private def half (ε : Fin 8 → Bool) : Fin 8 → ℤ := fun k => sign (ε k)
private def satisfies (v : Fin 8 → ℤ) : Prop := v 0 + v 1 = 0
private instance (v : Fin 8 → ℤ) : Decidable (satisfies v) := inferInstanceAs (Decidable (_ = _))
private instance (ε : Fin 8 → Bool) : Decidable (evenNegative ε) :=
  inferInstanceAs (Decidable (Even ((Finset.univ.filter fun i => !(ε i)).card)))

private theorem coord_constraints : ∀ r, satisfies (coord r) := by decide +kernel
private def pairWitness (r : Fin 126) : Fin 8 × Fin 8 × Bool × Bool :=
  (#[(0, 1, false, true), (0, 1, true, false), (2, 3, false, false), (2, 3, false, true), (2, 3, true, false), (2, 3, true, true), (2, 4, false, false), (2, 4, false, true), (2, 4, true, false), (2, 4, true, true), (2, 5, false, false), (2, 5, false, true), (2, 5, true, false), (2, 5, true, true), (2, 6, false, false), (2, 6, false, true), (2, 6, true, false), (2, 6, true, true), (2, 7, false, false), (2, 7, false, true), (2, 7, true, false), (2, 7, true, true), (3, 4, false, false), (3, 4, false, true), (3, 4, true, false), (3, 4, true, true), (3, 5, false, false), (3, 5, false, true), (3, 5, true, false), (3, 5, true, true), (3, 6, false, false), (3, 6, false, true), (3, 6, true, false), (3, 6, true, true), (3, 7, false, false), (3, 7, false, true), (3, 7, true, false), (3, 7, true, true), (4, 5, false, false), (4, 5, false, true), (4, 5, true, false), (4, 5, true, true), (4, 6, false, false), (4, 6, false, true), (4, 6, true, false), (4, 6, true, true), (4, 7, false, false), (4, 7, false, true), (4, 7, true, false), (4, 7, true, true), (5, 6, false, false), (5, 6, false, true), (5, 6, true, false), (5, 6, true, true), (5, 7, false, false), (5, 7, false, true), (5, 7, true, false), (5, 7, true, true), (6, 7, false, false), (6, 7, false, true), (6, 7, true, false), (6, 7, true, true), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false), (0, 1, false, false)] : Array (Fin 8 × Fin 8 × Bool × Bool))[r.val]!
private def signs (r : Fin 126) (q : Fin 8) : Bool := decide (0 < coord r q)
private theorem coord_pair_or_half : ∀ r : Fin 126,
    (∃ i j : Fin 8, ∃ a b : Bool, i ≠ j ∧ coord r = pair i j a b) ∨
      ∃ ε : Fin 8 → Bool, evenNegative ε ∧ coord r = half ε := by
  have hc : ∀ r : Fin 126,
      ((pairWitness r).1 ≠ (pairWitness r).2.1 ∧
        coord r = pair (pairWitness r).1 (pairWitness r).2.1 (pairWitness r).2.2.1 (pairWitness r).2.2.2) ∨
      (evenNegative (signs r) ∧ coord r = half (signs r)) := by decide +kernel
  intro r
  rcases hc r with hp | hh
  · exact Or.inl ⟨_, _, _, _, hp⟩
  · exact Or.inr ⟨_, hh⟩

private theorem pair_complete : ∀ (i j : Fin 8) (a b : Bool),
    i ≠ j → satisfies (pair i j a b) → ∃ r, coord r = pair i j a b := by
  decide +kernel

private theorem half_complete : ∀ ε : Fin 8 → Bool,
    evenNegative ε → satisfies (half ε) → ∃ r, coord r = half ε := by
  decide +kernel

noncomputable def realCoord (r : Fin 126) : Vec 8 := fun k => (coord r k : ℝ) / 2

private theorem pair_cast (i j : Fin 8) (a b : Bool) (k : Fin 8) :
    ((pair i j a b k : ℤ) : ℝ) / 2 =
      ((sign a : ℤ) : ℝ) * basisVector i k + ((sign b : ℤ) : ℝ) * basisVector j k := by
  simp only [pair, basisVector, Pi.single_apply, Int.cast_add, Int.cast_ite, Int.cast_mul,
    Int.cast_ofNat, Int.cast_zero]
  split_ifs <;> ring

private theorem half_cast (ε : Fin 8 → Bool) (k : Fin 8) :
    ((half ε k : ℤ) : ℝ) / 2 = halfSignVector ε k := by
  simp only [half, sign, halfSignVector]
  cases ε k <;> norm_num

private theorem constraints_real (v : Vec 8) :
    dot v (basisVector 0 + basisVector 1) = 0 ↔ v 0 + v 1 = 0 := by
  simp [dot, basisVector, Pi.single_apply, mul_add, Finset.sum_add_distrib]

/-- Every listed coordinate is an actual root of the standard E7 pairing. -/
theorem realCoord_mem (r : Fin 126) : realCoord r ∈ typeE7Roots := by
  have hc : realCoord r 0 + realCoord r 1 = 0 := by
    have h := coord_constraints r
    have h' : (coord r 0 : ℝ) + (coord r 1 : ℝ) = 0 := by exact_mod_cast h
    dsimp only [realCoord]
    linarith
  refine ⟨?_, (constraints_real (realCoord r)).mpr hc⟩
  rcases coord_pair_or_half r with ⟨i, j, a, b, hij, he⟩ | ⟨ε, hε, he⟩
  · left
    refine ⟨i, j, hij, (sign a : ℤ), (sign b : ℤ), ?_, ?_, ?_⟩
    · cases a <;> norm_num [sign]
    · cases b <;> norm_num [sign]
    · funext k
      simp only [realCoord, he, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact pair_cast i j a b k
  · right
    refine ⟨ε, hε, ?_⟩
    funext k
    simp only [realCoord, he]
    exact half_cast ε k

noncomputable def root (r : Fin 126) : typeE7Roots := ⟨realCoord r, realCoord_mem r⟩

/-- Distinct finite labels represent distinct native roots. -/
theorem root_injective : Function.Injective root := by
  intro r s he
  have hc : coord r = coord s := by
    funext k
    have hk := congrArg (fun t : typeE7Roots => t.val k) he
    change (coord r k : ℝ) / 2 = (coord s k : ℝ) / 2 at hk
    have h' : (coord r k : ℝ) = (coord s k : ℝ) := by linarith
    exact_mod_cast h'
  exact (by decide +kernel : Function.Injective coord) hc

/-- Every native E7 root occurs in the literal finite catalogue. -/
theorem root_surjective : Function.Surjective root := by
  rintro ⟨v, ⟨hv, h01⟩⟩
  have hc := (constraints_real v).mp h01
  suffices ∃ r, realCoord r = v by
    obtain ⟨r, hr⟩ := this
    exact ⟨r, Subtype.ext hr⟩
  rcases hv with ⟨i, j, hij, a, b, ha, hb, hv⟩ | ⟨ε, hε, hv⟩
  · have hs (x : ℝ) (hx : x ∈ ({-1, 1} : Set ℝ)) : ∃ t : Bool, x = (sign t : ℤ) := by
      rcases hx with h | h
      · exact ⟨false, by simpa only [Set.mem_singleton_iff, sign, Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_one] using h⟩
      · exact ⟨true, by simpa only [Set.mem_singleton_iff, sign, ↓reduceIte, Int.cast_one] using h⟩
    obtain ⟨a, rfl⟩ := hs a ha
    obtain ⟨b, rfl⟩ := hs b hb
    have hcoord (k : Fin 8) : ((pair i j a b k : ℤ) : ℝ) = 2 * v k := by
      have h := pair_cast i j a b k
      rw [hv] at *
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
      linarith
    have hp : satisfies (pair i j a b) := by
      have h : ((pair i j a b 0 : ℤ) : ℝ) + ((pair i j a b 1 : ℤ) : ℝ) = 0 := by
        rw [hcoord, hcoord]
        linarith [hc]
      exact_mod_cast h
    obtain ⟨r, hr⟩ := pair_complete i j a b hij hp
    refine ⟨r, ?_⟩
    funext k
    dsimp only [realCoord]
    rw [hr, hcoord]
    ring
  · have hcoord (k : Fin 8) : ((half ε k : ℤ) : ℝ) = 2 * v k := by
      have h := half_cast ε k
      rw [hv]
      linarith
    have hp : satisfies (half ε) := by
      have h : ((half ε 0 : ℤ) : ℝ) + ((half ε 1 : ℤ) : ℝ) = 0 := by
        rw [hcoord, hcoord]
        linarith [hc]
      exact_mod_cast h
    obtain ⟨r, hr⟩ := half_complete ε hε hp
    refine ⟨r, ?_⟩
    funext k
    dsimp only [realCoord]
    rw [hr, hcoord]
    ring

/-- The native root enumeration used by all subsequent matrix comparisons. -/
noncomputable def rootEquiv : Fin 126 ≃ typeE7Roots :=
  Equiv.ofBijective root ⟨root_injective, root_surjective⟩

end Theory.SpecificGroups.LieType.SourceLevi.E7.Operators.Coordinates
