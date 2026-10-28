module
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

/-!
# Four possible weight patterns for a six-dimensional J₂ representation

The order-six rotation (a,b) ↦ (b,b−a) has four orbits on the nonzero
vectors of F₅², each of size six. An invariant multiplicity function of total
weight six, not supported only at zero, is the indicator of exactly one orbit.
The proof checks the finite orbit bijection and uses the dimension sum; it
never enumerates functions with values in the natural numbers.

The fiber counts record restriction to x and d=xy⁻². They distinguish the
one- and two-dimensional x-spaces needed for the cubic calculation. The
outer normalizer permutes the four patterns in two pairs.

`WeightSpaces` applies the result to the eigenspaces of the literal ATLAS
carrier. Its spectral inputs and the exclusion of two patterns remain separate
obligations; these finite lemmas alone do not classify representations.

Source application: Aschbacher--Smith K.4.5, printed p.460, and Hiss--Malle,
corrected Table 2, degree-six characteristic-two J₂ entry. The rotation and
outer map are certified in `J2.TraceGeometry.Generators`.
-/

@[expose] public section
open scoped BigOperators
namespace Representation.JankoTwo.SixDimensionalCertificate.Weights
abbrev Weight := ZMod 5 × ZMod 5

def rotate (w : Weight) : Weight := (w.2, w.2 - w.1)

def seed : Fin 4 → Weight := ![(1,0),(2,0),(1,2),(2,4)]

def orbit (i : Fin 4) (j : Fin 6) : Weight := (rotate^[j.val]) (seed i)

def index : Option (Fin 4 × Fin 6) → Weight
  | none => 0
  | some (i,j) => orbit i j

theorem index_bijective : Function.Bijective index := by decide +kernel

theorem rotate_iterate_value (m : Weight → ℕ) (h : ∀ w, m (rotate w) = m w) (w : Weight) (n : ℕ) :
    m ((rotate^[n]) w) = m w := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', h, ih]

theorem sum_index (m : Weight → ℕ) :
    (∑ w, m w) = m 0 + ∑ i : Fin 4, ∑ j : Fin 6, m (orbit i j) := by
  rw [← Equiv.sum_comp (Equiv.ofBijective index index_bijective)]
  simp [index, Fintype.sum_prod_type]

theorem orbit_value (m : Weight → ℕ) (h : ∀ w, m (rotate w) = m w)
    (i : Fin 4) (j : Fin 6) : m (orbit i j) = m (seed i) :=
  rotate_iterate_value m h (seed i) j.val

theorem sum_rotation_invariant (m : Weight → ℕ) (h : ∀ w, m (rotate w) = m w) :
    (∑ w, m w) = m 0 + 6 * ∑ i : Fin 4, m (seed i) := by
  rw [sum_index]
  simp only [orbit_value m h, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]

def pattern (i : Fin 4) (w : Weight) : ℕ :=
  if w ∈ Finset.univ.image (orbit i) then 1 else 0

theorem pattern_zero : ∀ i, pattern i 0 = 0 := by decide +kernel

theorem pattern_orbit : ∀ i k j, pattern i (orbit k j) = if k = i then 1 else 0 := by
  decide +kernel

theorem four_patterns (m : Weight → ℕ) (h : ∀ w, m (rotate w) = m w)
    (hs : ∑ w, m w = 6) (hz : m 0 < 6) : ∃ i, m = pattern i := by
  have hh := sum_rotation_invariant m h
  rw [hs] at hh
  have hmzero : m 0 = 0 := by omega
  have hsum : ∑ i : Fin 4, m (seed i) = 1 := by omega
  have hsum' : m (seed 0) + m (seed 1) + m (seed 2) + m (seed 3) = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  obtain ⟨i, hi, ho⟩ : ∃ i : Fin 4, m (seed i) = 1 ∧
      ∀ k : Fin 4, k ≠ i → m (seed k) = 0 := by
    have hc : m (seed 0) = 1 ∨ m (seed 1) = 1 ∨ m (seed 2) = 1 ∨ m (seed 3) = 1 := by
      omega
    rcases hc with hc | hc | hc | hc
    · refine ⟨0, hc, ?_⟩
      intro k hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
        first | exact (hk rfl).elim | omega
    · refine ⟨1, hc, ?_⟩
      intro k hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
        first | exact (hk rfl).elim | omega
    · refine ⟨2, hc, ?_⟩
      intro k hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
        first | exact (hk rfl).elim | omega
    · refine ⟨3, hc, ?_⟩
      intro k hk
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;>
        first | exact (hk rfl).elim | omega
  refine ⟨i, ?_⟩
  funext w
  obtain ⟨j, rfl⟩ := index_bijective.surjective w
  cases j with
  | none => exact hmzero.trans (pattern_zero i).symm
  | some p =>
    rcases p with ⟨k,j⟩
    change m (orbit k j) = pattern i (orbit k j)
    rw [orbit_value m h, pattern_orbit]
    split_ifs with hk
    · simpa [hk] using hi
    · exact ho k hk

def xMultiplicity (i : Fin 4) (e : ZMod 5) : ℕ :=
  ∑ w : Weight, if w.1 = e then pattern i w else 0

def dExponent (w : Weight) : ZMod 5 := w.1 - 2 * w.2

theorem xMultiplicity_values : ∀ i,
    (fun e : Fin 5 => xMultiplicity i e.val) =
      (![![2,2,0,0,2], ![2,0,2,2,0], ![0,2,1,1,2], ![0,1,2,2,1]] :
        Fin 4 → Fin 5 → ℕ) i := by decide +kernel

theorem line_trivial_on_d : ∀ i w,
    pattern i w = 1 → xMultiplicity i w.1 = 1 → dExponent w = 0 := by
  decide +kernel

theorem plane_nontrivial_on_d : ∀ i w,
    pattern i w = 1 → xMultiplicity i w.1 = 2 → dExponent w ≠ 0 := by
  decide +kernel

def outerMap (w : Weight) : Weight := (3 * w.1 + 2 * w.2, 2 * w.2)
def swap : Fin 4 → Fin 4 := ![1,0,3,2]

theorem outerMap_patterns : ∀ i w, pattern i (outerMap w) = pattern (swap i) w := by
  decide +kernel

end Representation.JankoTwo.SixDimensionalCertificate.Weights
