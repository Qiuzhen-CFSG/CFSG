module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E8.Operators.Coordinates.Completeness
public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E8.Operators.Coordinates.Codes

/-!
# Exact coordinates for the E8 adjoint lattice

The 240 doubled integral root coordinates are 112 signed pair vectors
and 128 even half-sign vectors.
Explicit finite witnesses and completeness certificates identify this catalogue
with the literal standard root set. Its ordering matches the exceptional Levi
matrix calculation; the full Cartan-plus-root basis has dimension 248.
Source: the standard E8 root system and Geck's integral construction, GLS3 §2.6.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.SpecificGroups.LieType.SourceLevi.E8.Operators.Coordinates
open Certificates

noncomputable def realCoord (r : Fin 240) : Vec 8 := fun k => (coord r k : ℝ) / 2

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

/-- Every listed coordinate is an actual root of the standard E8 pairing. -/
theorem realCoord_mem (r : Fin 240) : realCoord r ∈ typeE8Roots := by
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

noncomputable def root (r : Fin 240) : typeE8Roots := ⟨realCoord r, realCoord_mem r⟩

/-- Distinct finite labels represent distinct native roots. -/
theorem root_injective : Function.Injective root := by
  intro r s he
  have hc : coord r = coord s := by
    funext k
    have hk := congrArg (fun t : typeE8Roots => t.val k) he
    change (coord r k : ℝ) / 2 = (coord s k : ℝ) / 2 at hk
    have h' : (coord r k : ℝ) = (coord s k : ℝ) := by linarith
    exact_mod_cast h'
  apply codeTable_injective
  rw [← coordinateCode_eq, ← coordinateCode_eq, hc]

/-- Every native E8 root occurs in the literal finite catalogue. -/
theorem root_surjective : Function.Surjective root := by
  rintro ⟨v, hv⟩

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
    obtain ⟨r, hr⟩ := pair_complete i j a b hij
    refine ⟨r, ?_⟩
    funext k
    dsimp only [realCoord]
    rw [hr, hcoord]
    ring
  · have hcoord (k : Fin 8) : ((half ε k : ℤ) : ℝ) = 2 * v k := by
      have h := half_cast ε k
      rw [hv]
      linarith
    obtain ⟨r, hr⟩ := half_complete ε hε
    refine ⟨r, ?_⟩
    funext k
    dsimp only [realCoord]
    rw [hr, hcoord]
    ring

/-- The native root enumeration used by all subsequent matrix comparisons. -/
noncomputable def rootEquiv : Fin 240 ≃ typeE8Roots :=
  Equiv.ofBijective root ⟨root_injective, root_surjective⟩

end Theory.SpecificGroups.LieType.SourceLevi.E8.Operators.Coordinates
