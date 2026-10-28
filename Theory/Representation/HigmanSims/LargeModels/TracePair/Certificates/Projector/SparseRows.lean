module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector.Sparse

/-!
# Sparse checks as packed row-product certificates

Equality of all decoded F₄ coordinates is equality of the two packed bit
planes. This turns the sparse checker into the usual row-product certificate,
so the sparse rows 560–583 and 715 can be assembled with their dense neighbors.
The actual consumer is the supplied degree-896 HS inverse witness in Inverse.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
open Packed
private theorem decode_eq_iff (a b : Row) (i : ℕ) :
    decode a i = decode b i ↔ a.1.testBit i = b.1.testBit i ∧ a.2.testBit i = b.2.testBit i := by
  unfold decode Base.entry
  unfold Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour.Packed.bit
  cases a.1.testBit i <;> cases a.2.testBit i <;>
    cases b.1.testBit i <;> cases b.2.testBit i <;> decide +kernel

private theorem decode_injective {a b : Row} (h : ∀ i, decode a i = decode b i) : a = b := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq
    intro i
    exact ((decode_eq_iff a b i).mp (h i)).1
  · apply Nat.eq_of_testBit_eq
    intro i
    exact ((decode_eq_iff a b i).mp (h i)).2

theorem checkRows_of_sparse (n : ℕ) (ts : List Terms) (a b c : Mat) (hb : b.length = n)
    (hs : checkSparse n ts a b c = true) : checkRows a b c = true := by
  induction a generalizing ts c with
  | nil => cases ts <;> cases c <;> simp_all [checkSparse, checkRows]
  | cons a as ih =>
    cases ts with
    | nil => simp [checkSparse] at hs
    | cons t ts =>
      cases c with
      | nil => simp [checkSparse] at hs
      | cons c cs =>
        have hp : product a b = c := by
          apply decode_injective
          intro j
          rw [product_eq, decode_rowProduct _ _ n hb]
          exact checkSparse_get n (t :: ts) (a :: as) b (c :: cs) hs 0 (by simp) j
        simp only [checkSparse, Bool.and_eq_true] at hs
        simp only [checkRows, hp, beq_self_eq_true, Bool.true_and]
        exact ih ts cs hs.2.2.2
end Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
