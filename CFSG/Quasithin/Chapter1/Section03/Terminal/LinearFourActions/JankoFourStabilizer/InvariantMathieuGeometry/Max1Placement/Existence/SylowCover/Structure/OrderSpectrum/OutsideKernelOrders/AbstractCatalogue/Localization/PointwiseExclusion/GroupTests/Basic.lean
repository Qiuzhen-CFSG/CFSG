module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.Interface

/-!
# Evaluation adapters for the pointwise coordinate calculations

Bit vectors encode the twenty-one Boolean coefficients of the original ascending
word. These lemmas identify single-bit monomials, preserve word evaluation across
bounded collection, and compare coordinates using the exact cardinal premise.
Source: the literal SylowNormalEights presentation; Aschbacher–Smith A.3.12,
pp.47–48. See ../source/README.md for the inverse-conjugation conventions.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests
open PointwiseCalculation Symbolic

def valuation (b : Boolean.Bits) : Monomial :=
  (BitVec.ofBoolListLE (List.ofFn b)).setWidth 42

theorem valuation_get (b : Boolean.Bits) (i : Fin 21) :
    (valuation b).getLsbD i.val = b i := by
  have hi : i.val < 42 := lt_trans i.isLt (by decide)
  simp only [valuation, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]

theorem mono_single (v : Monomial) (i : Fin 21) :
    monomialValue (BitVec.twoPow 42 i.val) v = v.getLsbD i.val := by
  have hi : i.val < 42 := lt_trans i.isLt (by decide)
  apply Bool.eq_iff_iff.mpr
  simp only [monomialValue, beq_iff_eq]
  constructor
  · intro h
    have hh := congrArg (fun t : Monomial => t.getLsbD i.val) h
    simpa [hi] using hh
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j _
    by_cases hj : i.val = j
    · subst j; simp [hi, h]
    · simp [hi, hj]

theorem mono_or (a b v : Monomial) :
    monomialValue (a ||| b) v = (monomialValue a v && monomialValue b v) := by
  have split_and : ∀ a b c : Bool, ((a || b) && c) = (a || b) →
      (a && c) = a ∧ (b && c) = b := by decide
  apply Bool.eq_iff_iff.mpr
  simp only [monomialValue, beq_iff_eq, Bool.and_eq_true]
  constructor
  · intro h
    constructor
    · apply BitVec.eq_of_getLsbD_eq
      intro i _
      have hi := congrArg (fun t : Monomial => t.getLsbD i) h
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] at hi ⊢
      exact (split_and _ _ _ hi).1
    · apply BitVec.eq_of_getLsbD_eq
      intro i _
      have hi := congrArg (fun t : Monomial => t.getLsbD i) h
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] at hi ⊢
      exact (split_and _ _ _ hi).2
  · rintro ⟨ha, hb⟩
    rw [BitVec.and_or_distrib_right, ha, hb]

def inputCoordinates (i : Fin 21) : Poly := [BitVec.twoPow 42 i.val]
def inputWord : Word := coordinates inputCoordinates

theorem value_inputWord (b : Boolean.Bits) :
    value inputWord (valuation b) = boolValue b := by
  rw [inputWord, value_coordinates]
  congr 1
  funext i
  simp only [inputCoordinates, polyValue_cons, polyValue_nil, Bool.xor_false,
    mono_single, valuation_get]

theorem value_of_collect (n : Nat) (u w : Word) (h : collect n u = w) (v : Monomial) :
    value w v = value u v := by
  rw [← h]
  exact collect_sound n u v

open Janko4.LocalStructure.SylowNormalEights Presentation

theorem boolValue_false : boolValue (fun _ => false) = 1 := by
  simp [boolValue]

theorem square_coordinates (hcard : Nat.card Carrier = 2^21)
    (p : Fin 21 → Poly)
    (hp : ∀ v, value (coordinates p) v = value (inputWord ++ inputWord) v)
    (b : Boolean.Bits) (hb : boolValue b ^ 2 = 1) (i : Fin 21) :
    polyValue (p i) (valuation b) = false := by
  have h : boolValue (fun i => polyValue (p i) (valuation b)) =
      boolValue (fun _ => false) := by
    rw [← value_coordinates, hp, value_append, value_inputWord, boolValue_false, ← pow_two]
    exact hb
  exact congrFun (boolValue_injective hcard h) i

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests
