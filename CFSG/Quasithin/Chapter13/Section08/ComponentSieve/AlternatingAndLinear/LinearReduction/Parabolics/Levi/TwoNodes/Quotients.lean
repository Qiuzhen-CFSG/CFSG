module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoNodes.Pairs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.FiveSpaces

/-!
# The marked quotient at two nonadjacent nodes in binary five-space

For every ordered nonadjacent pair, the actual parabolic modulo its intrinsic
two-core is S₃ × S₃. The homomorphism is the action on the two consecutive
coordinate blocks belonging to those nodes. The two formulas retain their
order, and a literal block-diagonal section lifts every pair of permutations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25,
printed pp.959–960 (PDF pp.976–977). This module establishes the quotient and
its geometric markings; it does not identify a whole single-node parabolic
with just one factor, or assert the images of its two-residual.
-/

@[expose] public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.SmallParabolicLevi BinaryLinear.SmallParabolicLevi.TwoNodes
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

/-- The two actual diagonal actions, ordered by the supplied nonadjacent nodes. -/
noncomputable def fiveTwoNodeBlockAction (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    fiveParabolic b {i, j} →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
  (pairFactorsEquiv i j h).toMonoidHom.comp (flagDiagonalAction b {i, j}ᶜ)

theorem fiveTwoNodeBlockAction_surjective (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Function.Surjective (fiveTwoNodeBlockAction b i j h) :=
  (pairFactorsEquiv i j h).surjective.comp (flagDiagonalAction_surjective b {i, j}ᶜ)

/-- The kernel is exactly the intrinsic two-core of the actual parabolic. -/
theorem ker_fiveTwoNodeBlockAction (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (fiveTwoNodeBlockAction b i j h).ker = pCore 2 (fiveParabolic b {i, j}) := by
  exact (MonoidHom.ker_comp_of_injective (flagDiagonalAction b {i, j}ᶜ)
    (pairFactorsEquiv i j h).toMonoidHom (pairFactorsEquiv i j h).injective).trans
      (ker_flagDiagonalAction b {i, j}ᶜ)

/-- The actual nonadjacent-node quotient, with both geometric factors marked. -/
noncomputable def fiveTwoNodeQuotientEquiv (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    (fiveParabolic b {i, j} ⧸ pCore 2 (fiveParabolic b {i, j})) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
  (flagDiagonalQuotientEquiv b {i, j}ᶜ).trans (pairFactorsEquiv i j h)

@[simp] theorem fiveTwoNodeQuotientEquiv_mk (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (g : fiveParabolic b {i, j}) :
    fiveTwoNodeQuotientEquiv b i j h (QuotientGroup.mk' _ g) =
      fiveTwoNodeBlockAction b i j h g := rfl

/-- The first S₃ factor is the action on the ordered coordinates `i,i+1`. -/
theorem fiveTwoNodeBlockAction_fst (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (g : fiveParabolic b {i, j}) :
    (fiveTwoNodeBlockAction b i j h g).1 =
      linearTwoEquivSymmetricThree (linearGroupCongr
        (nodeCoordinates i j h i (Or.inl rfl))
        (flagDiagonalAction b {i, j}ᶜ g (pairLabel i j i.castSucc))) := rfl

/-- The second S₃ factor is the action on the ordered coordinates `j,j+1`. -/
theorem fiveTwoNodeBlockAction_snd (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val) (g : fiveParabolic b {i, j}) :
    (fiveTwoNodeBlockAction b i j h g).2 =
      linearTwoEquivSymmetricThree (linearGroupCongr
        (nodeCoordinates i j h j (Or.inr rfl))
        (flagDiagonalAction b {i, j}ᶜ g (pairLabel i j j.castSucc))) := rfl

/-- A literal block-diagonal lift of any specified pair of permutations. -/
noncomputable def fiveTwoNodeSection (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val)
    (a : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) : fiveParabolic b {i, j} :=
  (flagCoordinates b {i, j}ᶜ).symm
    ⟨diagonalLift (pairLabel i j) ((pairFactorsEquiv i j h).symm a), diagonalLift_mem _ _⟩

@[simp] theorem fiveTwoNodeBlockAction_section (b : FiveBasis) (i j : Fin 4)
    (h : i.val + 1 < j.val ∨ j.val + 1 < i.val)
    (a : Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :
    fiveTwoNodeBlockAction b i j h (fiveTwoNodeSection b i j h a) = a := by
  change pairFactorsEquiv i j h (diagonalAction (pairLabel i j)
    (flagCoordinates b {i, j}ᶜ ((flagCoordinates b {i, j}ᶜ).symm
      ⟨diagonalLift (pairLabel i j) ((pairFactorsEquiv i j h).symm a),
        diagonalLift_mem _ _⟩))) = a
  rw [MulEquiv.apply_symm_apply]
  exact (congrArg (pairFactorsEquiv i j h)
    (diagonalAction_lift (pairLabel i j) ((pairFactorsEquiv i j h).symm a))).trans
      ((pairFactorsEquiv i j h).apply_symm_apply a)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics

end
