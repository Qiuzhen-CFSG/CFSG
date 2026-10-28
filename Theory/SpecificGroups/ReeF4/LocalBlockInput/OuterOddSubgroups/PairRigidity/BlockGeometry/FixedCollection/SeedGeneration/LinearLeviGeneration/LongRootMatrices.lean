module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.LinearLeviGeneration.Pinned
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.LinearLeviGeneration.LongRootMatrices.Comparison

/-!
# The faithful SL₂ comparison at the long F₄ end node

The explicit action on the full F₄ Cartan-plus-root lattice sends the upper
and lower transvections to the actual integral Geck root curves at ±α₀.
Transvection generation therefore puts its image in `SplitGroup`. A natural
root-string block makes the action faithful. This constructs exactly the
pinned witness consumed by `fixedLevi_linear_le_of_longRootMap`.

Source: GLS3 §§2.3–2.4, especially Table 2.4 type VI, and the common-lattice
subsystem argument in §2.6; `refs/KGroup/GLS3/chapter2.tex`.
-/

public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open LongRootMatrices

private lemma ambient_positive (m : ℕ) (t : CoefficientField m) :
    ambientHom (linearSLRoot m true t) =
      F4Chevalley.rootCurve (typeF4SimpleRootIndex 0) t := by
  rw [linearSLRoot, if_pos rfl, ambientHom_positive]
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple]

private lemma ambient_negative (m : ℕ) (t : CoefficientField m) :
    ambientHom (linearSLRoot m false t) =
      F4Chevalley.rootCurve
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0)
          (typeF4SimpleRootIndex 0)) t := by
  rw [linearSLRoot, if_neg Bool.false_ne_true, ambientHom_negative]
  simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
    ← typeF4RootPairing_baseEquiv_val]
  simpa only [RootPairing.indexNeg_neg] using
    (rootCurveUnit_neg_simple (typeF4RootPairing_baseEquiv 0) t).symm

private lemma ambient_mem (m : ℕ) (A : LinearSL m) :
    ambientHom A ∈ SplitGroup m := by
  apply Matrix.SL2.transvection_induction
    (fun A : LinearSL m => ambientHom A ∈ SplitGroup m) ?_ ?_ A
  · intro i j hij t
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change ambientHom (linearSLRoot m true t) ∈ SplitGroup m
      rw [ambient_positive]
      exact rootGenerator_mem m (typeF4SimpleRootIndex 0, t)
    · change ambientHom (linearSLRoot m false t) ∈ SplitGroup m
      rw [ambient_negative]
      exact rootGenerator_mem m
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0)
          (typeF4SimpleRootIndex 0), t)
    · exact (hij rfl).elim
  · intro A B hA hB
    rw [map_mul]
    exact (SplitGroup m).mul_mem hA hB

/-- The faithful matrix homomorphism, restricted to the actual split F₄ group. -/
def linearLongRootHom (m : ℕ) : LinearSL m →* SplitGroup m :=
  ambientHom.codRestrict (SplitGroup m) (ambient_mem m)

lemma linearLongRootHom_injective (m : ℕ) :
    Function.Injective (linearLongRootHom m) := by
  intro A B h
  exact ambientHom_injective (congrArg Subtype.val h)

lemma linearLongRootHom_positive (m : ℕ) (t : CoefficientField m) :
    linearLongRootHom m (linearSLRoot m true t) =
      rootGeneratorInGroup m (typeF4SimpleRootIndex 0) t :=
  Subtype.ext (ambient_positive m t)

lemma linearLongRootHom_negative (m : ℕ) (t : CoefficientField m) :
    linearLongRootHom m (linearSLRoot m false t) =
      rootGeneratorInGroup m
        (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex 0)
          (typeF4SimpleRootIndex 0)) t :=
  Subtype.ext (ambient_negative m t)

/-- The required pinned faithful SL₂ map. The matrix construction also works
at `m = 0`; the displayed range is the one used by the nonbinary consumer. -/
def linearLongRootMap (m : ℕ) (_hm : 1 ≤ m) : LinearLongRootMap m where
  hom := linearLongRootHom m
  injective := linearLongRootHom_injective m
  positive := linearLongRootHom_positive m
  negative := linearLongRootHom_negative m

end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
