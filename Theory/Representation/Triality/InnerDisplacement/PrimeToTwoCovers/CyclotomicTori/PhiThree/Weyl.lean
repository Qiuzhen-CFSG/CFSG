module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.MatrixRealization
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.RootConjugation.RootCurves

/-!
# The cubic twisting word for the third cyclotomic torus

The word (s₁s₀s₂s₃)² is graph-field fixed and has cube one in the
literal split Geck group, at every binary parameter. These identities
are lifted from its action on the 24 roots using the faithful Weyl
realization. They specify the same twist as the existing q = 2
seven-plane, without specializing the coefficient field.

Source: the D₄ graph-field conventions in GLS3 §2.2 and the nonsplit
torus construction in `Triality.Standard.BinarySevenPlane.Weyl`.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree
open Triality.Standard Triality.Standard.ConcreteBruhat
open Triality.Standard.ConcreteBruhat.MatrixRealization
open Triality.Standard.Parabolics Triality.Standard.PositiveCoordinates.SumExchangeData
noncomputable section

/-- A word in the original simple Weyl representatives. -/
def word (n : ℕ) (hn : 0 < n) (l : List (Fin 4)) :
    SplitGroup (binaryParameters n hn) :=
  ((l.map (splitWeylGenerator (binaryParameters n hn))).prod :
    splitWeylSubgroup (binaryParameters n hn)).val

def rootWord (l : List (Fin 4)) : rootWeylGroup := (l.map rootWeylGenerator).prod

def permWord : List (Fin 4) → Fin 24 → Fin 24
  | [], r => r
  | i :: l, r => reflectionTable i (permWord l r)

theorem word_nil (n : ℕ) (hn : 0 < n) : word n hn [] = 1 := rfl

theorem word_cons (n : ℕ) (hn : 0 < n) (i : Fin 4) (l) :
    word n hn (i :: l) = weylWord (binaryParameters n hn) i 1 * word n hn l := rfl

theorem word_append (n : ℕ) (hn : 0 < n) (l m) :
    word n hn (l ++ m) = word n hn l * word n hn m := by
  simp only [word, List.map_append, List.prod_append, Subgroup.coe_mul]

theorem rootAction_rootWord (l) (r) : rootAction (rootWord l) r = permWord l r := by
  induction l with
  | nil => simp [rootWord, permWord]
  | cons i l ih =>
    change rootAction (rootWeylGenerator i * rootWord l) r = _
    rw [map_mul, Equiv.Perm.mul_apply, rootAction_simple, ih]
    rfl

theorem word_eq (n : ℕ) (hn : 0 < n) {l m}
    (h : ∀ r, permWord l r = permWord m r) : word n hn l = word n hn m := by
  apply congrArg Subtype.val
  apply (splitWeylEquiv (binaryParameters n hn) rfl).injective
  have he (l) : splitWeylEquiv (binaryParameters n hn) rfl
      (l.map (splitWeylGenerator (binaryParameters n hn))).prod = rootWord l := by
    induction l with
    | nil => exact map_one _
    | cons i l ih =>
      change splitWeylEquiv (binaryParameters n hn) rfl
        (splitWeylGenerator (binaryParameters n hn) i * _) = rootWeylGenerator i * _
      rw [map_mul]
      exact congrArg₂ (· * ·) (splitWeylEquiv_generator (binaryParameters n hn) rfl i) ih
  rw [he, he]
  apply rootAction_injective
  apply Equiv.ext
  intro r
  simpa only [rootAction_rootWord] using h r

theorem graphField_word (n : ℕ) (hn : 0 < n) (l) :
    graphFieldAutomorphism (binaryParameters n hn) (word n hn l) =
      word n hn (l.map typeD4DiagramPermutation) := by
  induction l with
  | nil => exact map_one _
  | cons i l ih =>
    simpa only [word_cons, List.map_cons, map_mul, graphField_weylWord, map_one] using
      congrArg (fun g => weylWord (binaryParameters n hn) (typeD4DiagramPermutation i) 1 * g) ih

/-- The graph-fixed order-three word used for both descent and conjugation. -/
def twistWord (n : ℕ) (hn : 0 < n) : SplitGroup (binaryParameters n hn) :=
  word n hn [1, 0, 2, 3, 1, 0, 2, 3]

theorem graphField_twistWord (n : ℕ) (hn : 0 < n) :
    graphFieldAutomorphism (binaryParameters n hn) (twistWord n hn) = twistWord n hn := by
  rw [twistWord, graphField_word]
  apply word_eq
  decide +kernel

theorem twistWord_cube (n : ℕ) (hn : 0 < n) : twistWord n hn ^ 3 = 1 := by
  rw [pow_succ, pow_two, twistWord, ← word_append, ← word_append, ← word_nil n hn]
  apply word_eq
  decide +kernel

theorem realizes_word (n : ℕ) (hn : 0 < n) (l) :
    Realizes (binaryParameters n hn) (word n hn l) (rootWord l) := by
  induction l with
  | nil => exact realizes_one _
  | cons i l ih => exact realizes_mul (realizes_simple _ rfl i) ih

end
end Triality.InnerDisplacement.PrimeToTwoCovers.CyclotomicTori.PhiThree
