/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.Automorphisms

/-!
# Lifting every Golay coordinate automorphism

The difference of the Parker factor set and its pullback has zero associator,
is symmetric, and has zero diagonal. Splitting this binary cocycle supplies a
sign correction and hence a standard lift of each concrete code automorphism.
The projection is therefore surjective; no group section is asserted.
Source: Aschbacher, Lemma 12.16 and the setup of Sections 14 and 27.

Adapted from Gerald Höhn, ATLAS, `Atlas/Fischer/ParkerMathieuLiftExistence.lean`, `Atlas/Fischer/ParkerStandardSurjectivity.lean`,
revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Changes: CFSG module imports, local triality namespace, Lean 4.33 proof syntax,
and compatibility with the existing concrete `IsStandard` predicate.
-/

@[expose] public section

noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin
open Atlas.Fischer Atlas.Codes
open scoped BigOperators

/-- The actual half-overlap invariant is preserved by the marked code action. -/
theorem parkerCodeEquiv_halfOverlap (g : Mathieu24CodeModel) (a b : golay) :
    golayHalfOverlap (parkerCodeEquiv g a) (parkerCodeEquiv g b)=golayHalfOverlap a b := by
  have he : overlap (parkerCodeEquiv g a : BinaryWord) (parkerCodeEquiv g b : BinaryWord)=
      overlap a.val b.val := by
    rw [overlap_eq_sum,overlap_eq_sum]
    exact Equiv.sum_comp g.val.symm (fun p => if a.val p ≠ 0 ∧ b.val p ≠ 0 then 1 else 0)
  unfold golayHalfOverlap
  rw [he]

/-- The actual quarter-weight invariant is preserved by the marked code action. -/
theorem parkerCodeEquiv_quarterWeight (g : Mathieu24CodeModel) (a : golay) :
    golayQuarterWeight (parkerCodeEquiv g a)=golayQuarterWeight a := by
  unfold golayQuarterWeight
  rw [parkerCodeEquiv_weight]

/-- Difference between the factor set and its pullback by an actual Mathieu
code automorphism. It is a cocycle although the factor set itself has the
nontrivial Parker associator. -/
def parkerMathieuFactorDifference (g : Mathieu24CodeModel) (a b : golay) : Bit :=
  parkerGolayFactorSet (parkerCodeEquiv g a) (parkerCodeEquiv g b)+parkerGolayFactorSet a b

@[simp] theorem parkerMathieuFactorDifference_zero (g : Mathieu24CodeModel) (a : golay) :
    parkerMathieuFactorDifference g 0 a=0 := by
  simp [parkerMathieuFactorDifference]

theorem parkerMathieuFactorDifference_symmetric (g : Mathieu24CodeModel) (a b : golay) :
    parkerMathieuFactorDifference g a b=parkerMathieuFactorDifference g b a := by
  have he : parkerMathieuFactorDifference g a b+parkerMathieuFactorDifference g b a=0 := by
    unfold parkerMathieuFactorDifference
    calc
      _ = (parkerGolayFactorSet (parkerCodeEquiv g a) (parkerCodeEquiv g b)+
          parkerGolayFactorSet (parkerCodeEquiv g b) (parkerCodeEquiv g a))+
          (parkerGolayFactorSet a b+parkerGolayFactorSet b a) := by abel
      _ = golayHalfOverlap a b+golayHalfOverlap a b := by
        rw [parkerGolayFactorSet_commutator,parkerGolayFactorSet_commutator,
          parkerCodeEquiv_halfOverlap]
      _ = 0 := CharTwo.add_self_eq_zero _
  exact (eq_neg_of_add_eq_zero_left he).trans (CharTwo.neg_eq _)

@[simp] theorem parkerMathieuFactorDifference_diagonal (g : Mathieu24CodeModel) (a : golay) :
    parkerMathieuFactorDifference g a a=0 := by
  unfold parkerMathieuFactorDifference
  rw [parkerGolayFactorSet_square,parkerGolayFactorSet_square,parkerCodeEquiv_quarterWeight]
  exact CharTwo.add_self_eq_zero _

theorem parkerMathieuFactorDifference_cocycle (g : Mathieu24CodeModel) (a b c : golay) :
    parkerMathieuFactorDifference g a b+parkerMathieuFactorDifference g (a+b) c+
      parkerMathieuFactorDifference g b c+parkerMathieuFactorDifference g a (b+c)=0 := by
  simp only [parkerMathieuFactorDifference,map_add]
  calc
    _ = (parkerGolayFactorSet (parkerCodeEquiv g a) (parkerCodeEquiv g b)+
        parkerGolayFactorSet (parkerCodeEquiv g a+parkerCodeEquiv g b) (parkerCodeEquiv g c)+
        parkerGolayFactorSet (parkerCodeEquiv g b) (parkerCodeEquiv g c)+
        parkerGolayFactorSet (parkerCodeEquiv g a) (parkerCodeEquiv g b+parkerCodeEquiv g c))+
        (parkerGolayFactorSet a b+parkerGolayFactorSet (a+b) c+
          parkerGolayFactorSet b c+parkerGolayFactorSet a (b+c)) := by abel
    _ = parkerTripleIntersection a b c+parkerTripleIntersection a b c := by
      rw [parkerGolayFactorSet_associator,parkerGolayFactorSet_associator,
        parkerCodeEquiv_triple]
    _ = 0 := CharTwo.add_self_eq_zero _

/-- Every actual Mathieu code automorphism has a normalized correcting sign
function. No existence or splitting of a known Parker extension is assumed. -/
theorem parkerMathieu_exists_correction (g : Mathieu24CodeModel) :
    ∃ η : golay → Bit, η 0=0 ∧ ∀ a b,
      η (a+b)+η a+η b=parkerMathieuFactorDifference g a b :=
  Atlas.Algebra.binary_cocycle_exists_correction (parkerMathieuFactorDifference g)
    (parkerMathieuFactorDifference_zero g) (parkerMathieuFactorDifference_symmetric g)
    (parkerMathieuFactorDifference_diagonal g) (parkerMathieuFactorDifference_cocycle g)

/-- A choice of lift corrections. This is a set-theoretic choice and carries
no assertion that the lifts compose as a group section. -/
def parkerMathieuSignCorrection (g : Mathieu24CodeModel) : golay → Bit :=
  Classical.choose (parkerMathieu_exists_correction g)

@[simp] theorem parkerMathieuSignCorrection_zero (g : Mathieu24CodeModel) :
    parkerMathieuSignCorrection g 0=0 := (Classical.choose_spec (parkerMathieu_exists_correction g)).1

theorem parkerMathieuSignCorrection_equation (g : Mathieu24CodeModel) (a b : golay) :
    parkerMathieuSignCorrection g (a+b)+parkerMathieuSignCorrection g a+
      parkerMathieuSignCorrection g b=parkerMathieuFactorDifference g a b :=
  (Classical.choose_spec (parkerMathieu_exists_correction g)).2 a b

/-- Actual permutation lift to the constructed marked Parker loop. -/
def parkerMathieuLift (g : Mathieu24CodeModel) : Equiv.Perm ParkerLoop :=
  parkerLoopLift (parkerCodeEquiv g) (parkerMathieuSignCorrection g)

@[simp] theorem parkerMathieuLift_code (g : Mathieu24CodeModel) (x : ParkerLoop) :
    (parkerMathieuLift g x).1=parkerCodeEquiv g x.1 := rfl

theorem parkerMathieuLift_multiply (g : Mathieu24CodeModel) (x y : ParkerLoop) :
    parkerMathieuLift g (parkerLoopMultiply x y)=
      parkerLoopMultiply (parkerMathieuLift g x) (parkerMathieuLift g y) :=
  parkerLoopLift_preserves_multiply _ _ (parkerMathieuSignCorrection_equation g) x y

theorem parkerMathieuLift_sign (g : Mathieu24CodeModel) (s : Bit) (x : ParkerLoop) :
    parkerMathieuLift g (parkerSign s x)=parkerSign s (parkerMathieuLift g x) :=
  parkerLoopLift_sign _ _ s x

@[simp] theorem parkerMathieuLift_fixes_sign (g : Mathieu24CodeModel) (s : Bit) :
    parkerMathieuLift g (0,s)=(0,s) :=
  parkerLoopLift_fixes_sign _ _ (parkerMathieuSignCorrection_zero g) s

end Sporadic.Monster.Construction.TrialitySpin

namespace Sporadic.Monster.Construction.TrialitySpin
open Atlas.Fischer Atlas.Codes

/-- A lift chosen separately for each element; no multiplicative section is asserted. -/
noncomputable def parkerStandardLift (g : Mathieu24CodeModel) : ParkerStandardGroup :=
  ⟨parkerMathieuLift g, (isStandard_iff _).mpr
    ⟨parkerMathieuLift_multiply g, parkerMathieuLift_fixes_sign g,
      g, parkerMathieuLift_code g⟩⟩

theorem parkerStandardProjection_lift (g : Mathieu24CodeModel) :
    parkerStandardProjection (parkerStandardLift g) = g := by
  apply parkerCodeEquiv_faithful
  intro a
  exact (parkerStandardProjection_spec (parkerStandardLift g) (a, 0)).symm

theorem parkerStandardProjection_surjective : Function.Surjective parkerStandardProjection := by
  intro g
  exact ⟨parkerStandardLift g, parkerStandardProjection_lift g⟩

end Sporadic.Monster.Construction.TrialitySpin
