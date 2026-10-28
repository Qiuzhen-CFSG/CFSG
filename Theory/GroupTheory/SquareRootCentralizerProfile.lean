module

public import Theory.GroupTheory.SquareRootCentralizerCharacteristic

/-!
# Counting square roots with a prescribed centralizer size

The number of square roots having a given centralizer cardinality is invariant
under group isomorphisms. A nonidentity central element is therefore fixed by
all automorphisms if this count distinguishes it from the other nonidentity
central elements. Unlike the constant-centralizer criterion, this also applies
when the marked element has square roots with several centralizer sizes.

Source: invariance of powers and commutation under group isomorphisms; motivated
by the nonsplit cyclic-four extensions of the Ree core.
-/

namespace Group

/-- Number of square roots of `z` whose centralizer has cardinality `n`. -/
public noncomputable def squareRootCommutingProfile {G : Type*} [Group G]
    (z : G) (n : ℕ) : ℕ := Nat.card {y : G // y ^ 2 = z ∧ commutingCard y = n}

/-- An isomorphism preserves every entry of the square-root centralizer profile. -/
public theorem squareRootCommutingProfile_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (z : G) (n : ℕ) :
    squareRootCommutingProfile (e z) n = squareRootCommutingProfile z n := by
  symm
  apply Nat.card_congr
  refine e.toEquiv.subtypeEquiv ?_
  intro y
  change (y ^ 2 = z ∧ commutingCard y = n) ↔
    ((e y) ^ 2 = e z ∧ commutingCard (e y) = n)
  rw [commutingCard_equiv, ← map_pow, e.injective.eq_iff]

/-- One profile entry distinguishing a nonidentity central mark makes it fixed. -/
public theorem fixed_of_squareRootCommutingProfile {G : Type*} [Group G]
    (z : G) (n m : ℕ) (hz : z ∈ Subgroup.center G) (hz1 : z ≠ 1)
    (hmark : squareRootCommutingProfile z n = m)
    (hother : ∀ x : G, x ∈ Subgroup.center G → x ≠ 1 → x ≠ z →
      squareRootCommutingProfile x n ≠ m)
    (a : MulAut G) : a z = z := by
  have hc : a z ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := a.surjective y
    simpa only [map_mul] using congrArg a (Subgroup.mem_center_iff.mp hz x)
  have hn : a z ≠ 1 := by
    intro h
    apply hz1
    apply a.injective
    simpa only [map_one] using h
  by_contra he
  apply hother (a z) hc hn he
  rw [squareRootCommutingProfile_equiv, hmark]

end Group
