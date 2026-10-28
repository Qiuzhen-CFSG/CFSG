module

public import Theory.AlgebraicGroup.RootSystems.IntegralChevalleyBrackets

/-!
# Integral all-root Chevalley transport package

This module is the public assembly point for the integral all-root Chevalley construction on
the Geck carrier `(b.support ⊕ ι) → ℤ`.  For a finite reduced crystallographic root pairing
with a chosen base, it re-exports the concrete Tits braid and cancellation identities, the
root-indexed operators and divided powers, their integral root-string actions, the exact
opposite-root normalization, and the all-root bracket coefficient of absolute value `p + 1`.

The additional theorem below makes root-line coherence explicit: every Tits word carrying a
root `j` to a root `k` carries the standard vector on the `j`-line to the canonical vector on
the `k`-line up to an integral sign whose square is one.  It combines the signed Tits action
from `IntegralGeckConstruction` with the canonical-route sign theorem.  The imported
Matsumoto argument makes the chosen reduced-route matrices independent of their reduced
spellings.  All arguments are componentwise and require no irreducibility hypothesis, so the
package applies unchanged to reducible pairings.
-/

namespace RootPairing.IntegralGeckConstruction

@[expose] public section

noncomputable section

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- Any Tits-word transport to a root agrees with the canonical root vector up to sign. -/
lemma exists_sign_rootVector_eq_smul_transportedVector
    (word : List b.support) {j k : ι}
    (hjk : reflectionWord (P := P) word j = k) :
    ∃ s : ℤ, s * s = 1 ∧
      rootVector (P := P) (b := b) k =
        s • transportedVector (P := P) word (v (b := b) j) := by
  rcases exists_rootVector_sign (P := P) (b := b) k with
    ⟨sk, hsk, hk⟩
  let a := titsWordSign (P := P) word j
  have ha : a * a = 1 := titsWordSign_mul_self word j
  have htransport : transportedVector (P := P) word (v (b := b) j) =
      a • v (b := b) k := by
    rw [transportedVector, titsWord_mulVec_v, hjk]
  refine ⟨sk * a, ?_, ?_⟩
  · calc
      (sk * a) * (sk * a) = (sk * sk) * (a * a) := by ring
      _ = 1 := by rw [hsk, ha]; norm_num
  · rw [hk, htransport, smul_smul, mul_assoc, ha, mul_one]

end


end


end RootPairing.IntegralGeckConstruction
