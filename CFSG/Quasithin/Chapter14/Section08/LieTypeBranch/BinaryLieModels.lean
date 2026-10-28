module

public import CFSG.KnownSimple.ClassicalModels
public import CFSG.KnownSimple.ExceptionalModels
public import CFSG.Quasithin.ClassificationModels

/-!
# The characteristic-two Lie-family input to Theorem D

This is the full Lie-family input over `q = 2^n`, used with `n > 1` in
Hypothesis 13.3.1(2). Each constructor records an actual model equivalence.
It places no upper bound on Lie rank and no restriction on the unitary-five
parameter. The classical ranges retain the low-rank aliases; they must be
handled through their actual carriers in the proof. The small derived
endpoints at q = 2 do not occur under the strict exponent hypothesis.

For unitary and twisted E6 groups, q is the fixed-field parameter, not the
matrix coefficient-field order. Suzuki and Ree F4 retain their odd field
exponents, and triality uses the genuine graph-field model.

Source: Aschbacher–Smith Hypothesis 13.3.1(2) and Theorem D/14.8.2(1),
printed pp.884 and 1078–1079; known Lie-family ranges as in the imported
catalogue (GLS3, Theorem 2.2.7). This definition is an input boundary, not
a rank restriction or a classification theorem.
-/

@[expose] public section

universe u v
namespace CFSG.Quasithin.Chapter14.Section08.LieTypeBranch

/-- All genuine characteristic-two simple Lie families at a fixed exponent.
The source application supplies `1 < n` and simplicity separately. -/
inductive IsBinaryLieModelAt (G : Type u) [Group G] (n : ℕ) : Prop
  | linear (d : ℕ) (hd : 2 ≤ d) (iso : ClassicalGroup.IsPSL G d (2 ^ n))
  | unitary (d : ℕ) (hd : 2 ≤ d) (iso : ClassicalGroup.IsPSU G d (2 ^ n))
  | symplectic (r : ℕ) (hr : 1 ≤ r) (iso : ClassicalGroup.IsPSp G r (2 ^ n))
  | orthogonalPlus (r : ℕ) (hr : 3 ≤ r)
      (iso : ClassicalGroup.IsPOmegaPlus G r (2 ^ n))
  | orthogonalOdd (r : ℕ) (hr : 1 ≤ r)
      (iso : ClassicalGroup.IsPOmegaOdd G r (2 ^ n))
  | orthogonalMinus (r : ℕ) (hr : 2 ≤ r)
      (iso : ClassicalGroup.IsPOmegaMinus G r (2 ^ n))
  | g2 (iso : ClassificationModels.IsG2At G (2 ^ n))
  | suzuki (m : ℕ) (hm : 1 ≤ m) (hn : n = 2 * m + 1)
      (iso : Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | triality (iso : Triality.Standard.IsTrialityGroupAt (2 ^ n) G)
  | reeF4 (m : ℕ) (hm : 1 ≤ m) (hn : n = 2 * m + 1)
      (iso : Nonempty (G ≃* ReeF4.Model m))
  | f4 (iso : ExceptionalGroup.IsF4 G (2 ^ n))
  | e6 (iso : ExceptionalGroup.IsE6 G (2 ^ n))
  | e7 (iso : ExceptionalGroup.IsE7 G (2 ^ n))
  | e8 (iso : ExceptionalGroup.IsE8 G (2 ^ n))
  | twistedE6 (iso : ExceptionalGroup.IsTwistedE6 G (2 ^ n))

/-- Transport the complete input without changing any field or rank parameter. -/
theorem IsBinaryLieModelAt.of_mulEquiv
    {G : Type u} {H : Type v} [Group G] [Group H] {n : ℕ}
    (h : IsBinaryLieModelAt G n) (e : H ≃* G) : IsBinaryLieModelAt H n := by
  cases h with
  | linear d hd iso => exact .linear d hd (iso.of_mulEquiv e)
  | unitary d hd iso => exact .unitary d hd (iso.of_mulEquiv e)
  | symplectic r hr iso => exact .symplectic r hr (iso.of_mulEquiv e)
  | orthogonalPlus r hr iso => exact .orthogonalPlus r hr (iso.of_mulEquiv e)
  | orthogonalOdd r hr iso => exact .orthogonalOdd r hr (iso.of_mulEquiv e)
  | orthogonalMinus r hr iso => exact .orthogonalMinus r hr (iso.of_mulEquiv e)
  | g2 iso => exact .g2 (iso.of_mulEquiv e)
  | suzuki m hm hn iso => exact .suzuki m hm hn (iso.map fun f => e.trans f)
  | triality iso => exact .triality (iso.of_mulEquiv e)
  | reeF4 m hm hn iso => exact .reeF4 m hm hn (iso.map fun f => e.trans f)
  | f4 iso => exact .f4 (iso.of_mulEquiv e)
  | e6 iso => exact .e6 (iso.of_mulEquiv e)
  | e7 iso => exact .e7 (iso.of_mulEquiv e)
  | e8 iso => exact .e8 (iso.of_mulEquiv e)
  | twistedE6 iso => exact .twistedE6 (iso.of_mulEquiv e)

end CFSG.Quasithin.Chapter14.Section08.LieTypeBranch
