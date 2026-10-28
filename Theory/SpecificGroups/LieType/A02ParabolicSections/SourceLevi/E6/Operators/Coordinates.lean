module

public import Theory.AlgebraicGroup.RootSystems.TypeE6RootPairing
public import Mathlib.Tactic

/-!
# Exact coordinates for the E₆ adjoint lattice

The 72 doubled integral root coordinates are the 40 signed pairs on the last
five Euclidean coordinates and the 32 even half-sign vectors satisfying the
two E₆ orthogonality equations. Finite integer certificates establish the
coordinate catalogue; casts identify it with the literal standard root set.
This enumeration fixes the 78-dimensional lattice used for the exceptional
Levi calculation in GLS3 §2.6 and Aschbacher–Smith A.2.18, printed p.40.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.SpecificGroups.LieType.SourceLevi.E6.Operators.Coordinates

def coord : Fin 72 → Fin 8 → ℤ :=
  ![![0, 0, 0, -2, -2, 0, 0, 0],
    ![0, 0, 0, -2, 2, 0, 0, 0],
    ![0, 0, 0, 2, -2, 0, 0, 0],
    ![0, 0, 0, 2, 2, 0, 0, 0],
    ![0, 0, 0, -2, 0, -2, 0, 0],
    ![0, 0, 0, -2, 0, 2, 0, 0],
    ![0, 0, 0, 2, 0, -2, 0, 0],
    ![0, 0, 0, 2, 0, 2, 0, 0],
    ![0, 0, 0, -2, 0, 0, -2, 0],
    ![0, 0, 0, -2, 0, 0, 2, 0],
    ![0, 0, 0, 2, 0, 0, -2, 0],
    ![0, 0, 0, 2, 0, 0, 2, 0],
    ![0, 0, 0, -2, 0, 0, 0, -2],
    ![0, 0, 0, -2, 0, 0, 0, 2],
    ![0, 0, 0, 2, 0, 0, 0, -2],
    ![0, 0, 0, 2, 0, 0, 0, 2],
    ![0, 0, 0, 0, -2, -2, 0, 0],
    ![0, 0, 0, 0, -2, 2, 0, 0],
    ![0, 0, 0, 0, 2, -2, 0, 0],
    ![0, 0, 0, 0, 2, 2, 0, 0],
    ![0, 0, 0, 0, -2, 0, -2, 0],
    ![0, 0, 0, 0, -2, 0, 2, 0],
    ![0, 0, 0, 0, 2, 0, -2, 0],
    ![0, 0, 0, 0, 2, 0, 2, 0],
    ![0, 0, 0, 0, -2, 0, 0, -2],
    ![0, 0, 0, 0, -2, 0, 0, 2],
    ![0, 0, 0, 0, 2, 0, 0, -2],
    ![0, 0, 0, 0, 2, 0, 0, 2],
    ![0, 0, 0, 0, 0, -2, -2, 0],
    ![0, 0, 0, 0, 0, -2, 2, 0],
    ![0, 0, 0, 0, 0, 2, -2, 0],
    ![0, 0, 0, 0, 0, 2, 2, 0],
    ![0, 0, 0, 0, 0, -2, 0, -2],
    ![0, 0, 0, 0, 0, -2, 0, 2],
    ![0, 0, 0, 0, 0, 2, 0, -2],
    ![0, 0, 0, 0, 0, 2, 0, 2],
    ![0, 0, 0, 0, 0, 0, -2, -2],
    ![0, 0, 0, 0, 0, 0, -2, 2],
    ![0, 0, 0, 0, 0, 0, 2, -2],
    ![0, 0, 0, 0, 0, 0, 2, 2],
    ![-1, 1, 1, -1, -1, -1, -1, -1],
    ![-1, 1, 1, -1, -1, -1, 1, 1],
    ![-1, 1, 1, -1, -1, 1, -1, 1],
    ![-1, 1, 1, -1, -1, 1, 1, -1],
    ![-1, 1, 1, -1, 1, -1, -1, 1],
    ![-1, 1, 1, -1, 1, -1, 1, -1],
    ![-1, 1, 1, -1, 1, 1, -1, -1],
    ![-1, 1, 1, -1, 1, 1, 1, 1],
    ![-1, 1, 1, 1, -1, -1, -1, 1],
    ![-1, 1, 1, 1, -1, -1, 1, -1],
    ![-1, 1, 1, 1, -1, 1, -1, -1],
    ![-1, 1, 1, 1, -1, 1, 1, 1],
    ![-1, 1, 1, 1, 1, -1, -1, -1],
    ![-1, 1, 1, 1, 1, -1, 1, 1],
    ![-1, 1, 1, 1, 1, 1, -1, 1],
    ![-1, 1, 1, 1, 1, 1, 1, -1],
    ![1, -1, -1, -1, -1, -1, -1, 1],
    ![1, -1, -1, -1, -1, -1, 1, -1],
    ![1, -1, -1, -1, -1, 1, -1, -1],
    ![1, -1, -1, -1, -1, 1, 1, 1],
    ![1, -1, -1, -1, 1, -1, -1, -1],
    ![1, -1, -1, -1, 1, -1, 1, 1],
    ![1, -1, -1, -1, 1, 1, -1, 1],
    ![1, -1, -1, -1, 1, 1, 1, -1],
    ![1, -1, -1, 1, -1, -1, -1, -1],
    ![1, -1, -1, 1, -1, -1, 1, 1],
    ![1, -1, -1, 1, -1, 1, -1, 1],
    ![1, -1, -1, 1, -1, 1, 1, -1],
    ![1, -1, -1, 1, 1, -1, -1, 1],
    ![1, -1, -1, 1, 1, -1, 1, -1],
    ![1, -1, -1, 1, 1, 1, -1, -1],
    ![1, -1, -1, 1, 1, 1, 1, 1]]

private def sign (a : Bool) : ℤ := if a then 1 else -1
private def pair (i j : Fin 8) (a b : Bool) : Fin 8 → ℤ :=
  fun k => (if k = i then 2 * sign a else 0) + (if k = j then 2 * sign b else 0)
private def half (ε : Fin 8 → Bool) : Fin 8 → ℤ := fun k => sign (ε k)
private def satisfies (v : Fin 8 → ℤ) : Prop := v 0 + v 1 = 0 ∧ v 1 - v 2 = 0
private instance (v : Fin 8 → ℤ) : Decidable (satisfies v) := inferInstanceAs (Decidable (_ ∧ _))
private instance (ε : Fin 8 → Bool) : Decidable (evenNegative ε) :=
  inferInstanceAs (Decidable (Even ((Finset.univ.filter fun i => !(ε i)).card)))

private theorem coord_constraints : ∀ r, satisfies (coord r) := by decide +kernel
private theorem coord_pair_or_half : ∀ r : Fin 72,
    (∃ i j : Fin 8, ∃ a b : Bool, i ≠ j ∧ coord r = pair i j a b) ∨
      ∃ ε : Fin 8 → Bool, evenNegative ε ∧ coord r = half ε := by
  decide +kernel

private theorem pair_complete : ∀ (i j : Fin 8) (a b : Bool),
    i ≠ j → satisfies (pair i j a b) → ∃ r, coord r = pair i j a b := by
  decide +kernel

private theorem half_complete : ∀ ε : Fin 8 → Bool,
    evenNegative ε → satisfies (half ε) → ∃ r, coord r = half ε := by
  decide +kernel

noncomputable def realCoord (r : Fin 72) : Vec 8 := fun k => (coord r k : ℝ) / 2

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
    dot v (basisVector 0 + basisVector 1) = 0 ∧
      dot v (basisVector 1 - basisVector 2) = 0 ↔
    v 0 + v 1 = 0 ∧ v 1 - v 2 = 0 := by
  simp [dot, basisVector, Pi.single_apply, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Every listed coordinate is an actual root of the standard E₆ pairing. -/
theorem realCoord_mem (r : Fin 72) : realCoord r ∈ typeE6Roots := by
  have hc : realCoord r 0 + realCoord r 1 = 0 ∧
      realCoord r 1 - realCoord r 2 = 0 := by
    have h := coord_constraints r
    dsimp only [satisfies] at h
    constructor
    · have h' : (coord r 0 : ℝ) + (coord r 1 : ℝ) = 0 := by exact_mod_cast h.1
      dsimp only [realCoord]
      linarith
    · have h' : (coord r 1 : ℝ) - (coord r 2 : ℝ) = 0 := by exact_mod_cast h.2
      dsimp only [realCoord]
      linarith
  have hd := (constraints_real (realCoord r)).mpr hc
  refine ⟨⟨?_, hd.1⟩, hd.2⟩
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

noncomputable def root (r : Fin 72) : typeE6Roots := ⟨realCoord r, realCoord_mem r⟩

/-- Distinct finite labels represent distinct native roots. -/
theorem root_injective : Function.Injective root := by
  intro r s he
  have hc : coord r = coord s := by
    funext k
    have hk := congrArg (fun t : typeE6Roots => t.val k) he
    change (coord r k : ℝ) / 2 = (coord s k : ℝ) / 2 at hk
    have h' : (coord r k : ℝ) = (coord s k : ℝ) := by linarith
    exact_mod_cast h'
  exact (by decide +kernel : Function.Injective coord) hc

/-- Every native E₆ root occurs in the literal finite catalogue. -/
theorem root_surjective : Function.Surjective root := by
  rintro ⟨v, ⟨⟨hv, h01⟩, h12⟩⟩
  have hc := (constraints_real v).mp ⟨h01, h12⟩
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
      constructor
      · have h : ((pair i j a b 0 : ℤ) : ℝ) + ((pair i j a b 1 : ℤ) : ℝ) = 0 := by rw [hcoord, hcoord]; linarith [hc.1]
        exact_mod_cast h
      · have h : ((pair i j a b 1 : ℤ) : ℝ) - ((pair i j a b 2 : ℤ) : ℝ) = 0 := by rw [hcoord, hcoord]; linarith [hc.2]
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
      constructor
      · have h : ((half ε 0 : ℤ) : ℝ) + ((half ε 1 : ℤ) : ℝ) = 0 := by rw [hcoord, hcoord]; linarith [hc.1]
        exact_mod_cast h
      · have h : ((half ε 1 : ℤ) : ℝ) - ((half ε 2 : ℤ) : ℝ) = 0 := by rw [hcoord, hcoord]; linarith [hc.2]
        exact_mod_cast h
    obtain ⟨r, hr⟩ := half_complete ε hε hp
    refine ⟨r, ?_⟩
    funext k
    dsimp only [realCoord]
    rw [hr, hcoord]
    ring

/-- The native root enumeration used by all subsequent matrix comparisons. -/
noncomputable def rootEquiv : Fin 72 ≃ typeE6Roots :=
  Equiv.ofBijective root ⟨root_injective, root_surjective⟩

end Theory.SpecificGroups.LieType.SourceLevi.E6.Operators.Coordinates
