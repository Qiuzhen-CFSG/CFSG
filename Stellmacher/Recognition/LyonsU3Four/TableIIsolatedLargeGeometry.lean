module
public import Stellmacher.Recognition.LyonsU3Four.TableILargeDifferenceGeometry

/-!
# Saturation by an isolated large-difference orbit

The four Galois translates of `(2,-1,0,-1)` are distinct and exhaust the
squared norms of both opposite-sum columns. Consequently, every other row
has vanishing opposite sums. This gives a finite-support route to the isolated
branch without discarding locally admissible rows prematurely.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
pp. 377–378, Cases 2(b), 3 and 4.
-/

@[expose] public section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
variable {I : Type*} [Fintype I] (d : GeneralizedDecompositionData I)

/-- Cyclic translates of the isolated large-difference row. -/
def isolatedDifferenceRow : Fin 4 → Fin 4 → ℤ :=
  ![![2,-1,0,-1], ![-1,0,-1,2], ![0,-1,2,-1], ![-1,2,-1,0]]

/-- A row belongs to the signed isolated orbit, or both opposite sums vanish. -/
def IsolatedDifferenceSupport (r : Fin 4 → ℤ) : Prop :=
  (∃ k : Fin 4, ∃ ε : ℤ, ε^2=1 ∧ r = fun i => ε * isolatedDifferenceRow k i) ∨
    (r 0 + r 2 = 0 ∧ r 1 + r 3 = 0)

/-- Multiplication by a row sign preserves the isolated support condition. -/
theorem IsolatedDifferenceSupport.mul {r : Fin 4 → ℤ}
    (h : IsolatedDifferenceSupport r) (ε : ℤ) (hε : ε^2=1) :
    IsolatedDifferenceSupport (fun i => ε * r i) := by
  rcases h with ⟨k, δ, hδ, rfl⟩ | ⟨ha, hb⟩
  · left
    refine ⟨k, ε*δ, ?_, ?_⟩
    · rw [mul_pow, hε, hδ, one_mul]
    · funext i; ring
  · right
    constructor
    · dsimp; rw [← mul_add, ha, mul_zero]
    · dsimp; rw [← mul_add, hb, mul_zero]

omit [Fintype I] in
private theorem isolated_orbit (hg : d.GaloisSymmetry) (hs : d.HasIsolatedLargeDifference) :
    ∃ (e : Fin 4 ↪ I) (ε : ℤ), ε^2=1 ∧
      ∀ k i, d.adjacentDifference i (e k) = ε * isolatedDifferenceRow k i := by
  obtain ⟨j, ε, hε, hj⟩ := hs
  obtain ⟨σ, hσ⟩ := hg.adjacentDifference d
  have hh (i : Fin 4) := congrFun hj i
  let e : Fin 4 → I := ![j, σ j, σ (σ j), σ (σ (σ j))]
  have he : ∀ k i, d.adjacentDifference i (e k) = ε * isolatedDifferenceRow k i := by
    intro k i
    fin_cases k <;> fin_cases i
    · exact hh 0
    · exact hh 1
    · exact hh 2
    · exact hh 3
    · exact (hσ j 1).symm.trans (hh 1)
    · exact (hσ j 2).symm.trans (hh 2)
    · exact (hσ j 3).symm.trans (hh 3)
    · exact (hσ j 0).symm.trans (hh 0)
    · exact (hσ (σ j) 1).symm.trans ((hσ j 2).symm.trans (hh 2))
    · exact (hσ (σ j) 2).symm.trans ((hσ j 3).symm.trans (hh 3))
    · exact (hσ (σ j) 3).symm.trans ((hσ j 0).symm.trans (hh 0))
    · exact (hσ (σ j) 0).symm.trans ((hσ j 1).symm.trans (hh 1))
    · exact (hσ (σ (σ j)) 1).symm.trans ((hσ (σ j) 2).symm.trans ((hσ j 3).symm.trans (hh 3)))
    · exact (hσ (σ (σ j)) 2).symm.trans ((hσ (σ j) 3).symm.trans ((hσ j 0).symm.trans (hh 0)))
    · exact (hσ (σ (σ j)) 3).symm.trans ((hσ (σ j) 0).symm.trans ((hσ j 1).symm.trans (hh 1)))
    · exact (hσ (σ (σ j)) 0).symm.trans ((hσ (σ j) 1).symm.trans ((hσ j 2).symm.trans (hh 2)))
  have hinj : Function.Injective e := by
    have hi : Function.Injective (fun k i => ε * isolatedDifferenceRow k i) := by
      rcases sq_eq_one_iff.mp hε with rfl | rfl <;> decide
    intro a b hab
    apply hi
    funext i
    change ε * isolatedDifferenceRow a i = ε * isolatedDifferenceRow b i
    rw [← he, ← he, hab]
  exact ⟨⟨e, hinj⟩, ε, hε, he⟩

/-- Four isolated Galois rows saturate the norms of the opposite sums. -/
theorem isolated_difference_support (h : d.Equation3_2) (hg : d.GaloisSymmetry)
    (hs : d.HasIsolatedLargeDifference) (x : I) :
    IsolatedDifferenceSupport (fun i => d.adjacentDifference i x) := by
  classical
  obtain ⟨e, ε, hε, he⟩ := d.isolated_orbit hg hs
  by_cases hx : ∃ k, x = e k
  · obtain ⟨k, rfl⟩ := hx
    exact Or.inl ⟨k, ε, hε, funext (he k)⟩
  · right
    have houtside (i : Fin 4) :
        d.adjacentDifference i x + d.adjacentDifference (oppositeDifferenceIndex i) x = 0 := by
      let f : I → ℤ := fun y =>
        d.adjacentDifference i y + d.adjacentDifference (oppositeDifferenceIndex i) y
      let s : Finset I := Finset.univ.image e
      have hn : ∑ k, f (e k)^2 = 16 := by
        dsimp [f]
        simp_rw [he]
        rcases sq_eq_one_iff.mp hε with rfl | rfl <;>
          fin_cases i <;> decide
      have hs' : ∑ y ∈ s, f y^2 = 16 := by
        rw [Finset.sum_image]
        · exact hn
        · exact fun a _ b _ hab => e.injective hab
      have hx' : x ∉ s := by simpa [s, eq_comm] using hx
      have hb : ∑ y ∈ insert x s, f y^2 ≤ 16 := by
        rw [← d.opposite_add_sq_sum h i]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
      rw [Finset.sum_insert hx', hs'] at hb
      change f x = 0
      nlinarith [sq_nonneg (f x)]
    exact ⟨houtside 0, houtside 1⟩

end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData
