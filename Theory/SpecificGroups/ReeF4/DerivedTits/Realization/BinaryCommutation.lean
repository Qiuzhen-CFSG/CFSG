module
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.Words
public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.CenterExponent.Layout
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus
-- Internal layout specification; no hidden definition is re-exposed.
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.RootAlignment

/-!
# An explicit outer centralizer for the short binary Ree root

The quartet and pair of index 3 commute. Their five split roots are
identified with the existing GLS root slots; all six pairwise inner products
are nonnegative. The characteristic-two Chevalley commutation theorem then
proves commutation of the actual root words. Explicit equality transport keeps
rewriting from unfolding the large canonical root expressions.

This provides the centralizing element used to correct a binary Ree conjugator
into the Tits derived subgroup. Source: GLS3 Table 2.4 and 2.4.5(d), and
Parrott (1972), §5, printed p.683.
-/

noncomputable section
namespace ReeF4.DerivedTits.Realization
open ReeF4 ReeF4.DerivedTits.Realization
open ReeF4.Parabolics.RadicalCoordinates.FixedCoordinates
open ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open ReeF4.NormalizedRootCentralizers.CenterExponent
open MatrixRelations.LongCommutators

private theorem positive_blocks : positiveRootWordLayout.blocks = rootBlocks .positive := by rfl
attribute [local irreducible] positiveRootWordLayout rootGeneratorInGroup X

private theorem q0 : quartetRoots 3 0 = R 6 := by
  have h := positiveRootWordLayout.quartet_long (3 : Fin 4)
  rw [positive_blocks, positive_quartet_indices] at h
  exact h
private theorem q1 : quartetRoots 3 1 = R 7 := by
  have h := positiveRootWordLayout.quartet_short (3 : Fin 4)
  rw [positive_blocks, positive_quartet_indices] at h
  exact h
private theorem q3 : quartetRoots 3 3 = R 9 := by
  have h := positiveRootWordLayout.quartet_high (3 : Fin 4)
  rw [positive_blocks, positive_quartet_indices] at h
  exact h
private theorem p0 : pairRoots 3 0 = R 10 := by
  have h := positiveRootWordLayout.pair_long (3 : Fin 4)
  rw [positive_blocks, positive_pair_indices] at h
  exact h
private theorem p1 : pairRoots 3 1 = R 11 := by
  have h := positiveRootWordLayout.pair_short (3 : Fin 4)
  rw [positive_blocks, positive_pair_indices] at h
  exact h

private theorem main_commute (i j : Fin 24)
    (hi : i = 6 ∨ i = 7 ∨ i = 9) (hj : j = 10 ∨ j = 11) :
    Commute (X 0 i 1) (X 0 j 1) := by
  apply xc
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl <;>
    norm_num [V, Theory.AlgebraicGroup.StandardRootSystem.dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]

private theorem commute_of_eq {G : Type*} [Mul G] {a b c d : G}
    (ha : a = c) (hb : b = d) (h : Commute c d) : Commute a b := by
  cases ha
  cases hb
  exact h

/-- The literal quartet word of index 3 centralizes the marked short-root word. -/
public theorem quartet_three_commutes_pair_three : Commute (quartetElement 3) (pairElement 3) := by
  have hq : quartetElement 3 = X 0 6 1 * X 0 7 1 * X 0 9 1 := by
    apply (quartetElement_eq 3).trans
    simp only [X]
    exact congrArg₂ (fun a b : SplitGroup 0 => a * b)
      (congrArg₂ (fun a b : SplitGroup 0 => a * b)
        (congrArg (fun r => rootGeneratorInGroup 0 r 1) q0)
        (congrArg (fun r => rootGeneratorInGroup 0 r 1) q1))
      (congrArg (fun r => rootGeneratorInGroup 0 r 1) q3)
  have hp : pairElement 3 = X 0 10 1 * X 0 11 1 := by
    apply (pairElement_eq 3).trans
    simp only [X]
    exact congrArg₂ (fun a b : SplitGroup 0 => a * b)
      (congrArg (fun r => rootGeneratorInGroup 0 r 1) p0)
      (congrArg (fun r => rootGeneratorInGroup 0 r 1) p1)
  apply commute_of_eq hq hp
  have h (i : Fin 24) (hi : i = 6 ∨ i = 7 ∨ i = 9) :
      Commute (X 0 i 1) (X 0 10 1 * X 0 11 1) :=
    (main_commute i 10 hi (Or.inl rfl)).mul_right (main_commute i 11 hi (Or.inr rfl))
  exact ((h 6 (Or.inl rfl)).mul_left (h 7 (Or.inr (Or.inl rfl)))).mul_left
    (h 9 (Or.inr (Or.inr rfl)))

end ReeF4.DerivedTits.Realization
