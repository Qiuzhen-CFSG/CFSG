module

public import Theory.SpecificGroups.Triality.OddFundamentalCentralizer

/-!
# The triality residual-rank contradiction in A.2.17

The source bounds the defining-characteristic rank of the prime-to-p
residual of the fundamental centralizer by one. The literal complementary
SL₂ over GF(q³) supplies rank at least 3e and contradicts this bound.

This is conditional assembly: the odd pinned maps and the commutation and
faithfulness of the specified complementary map still have to be constructed.
No centralizer identification or source exclusion is asserted from a family
label. The full residual equivalence is a separate structural obligation,
even though the contradiction itself only needs the embedded root subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.2.17, printed p.39 of `refs/quasithin.pdf`, especially (*) and
the final triality case.
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure.TrialityCentralizer
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.OddFundamentalCentralizer

variable {P : Parameters} (D : PinnedRankOneMaps P) (C : ArmRootCommutation P)

/-- Apply the cubic-field lower bound to the specified complementary map
and the source's literal residual, retaining the original field exponent. -/
theorem not_residual_rank_le_one
    (hcomm : ∀ a b, Commute (fundamentalHom D a) (complementHom D C b))
    (hj : Function.Injective (complementHom D C)) :
    ¬ primeRank P.prime (residual P) ≤ 1 := by
  intro hrank
  have hlo := three_mul_exponent_le_residual_rank D (complementHom D C) hcomm hj
  have he := P.exponent_pos
  omega

/-- The fundamental scalar is a genuine involution once the odd quotient
kernel calculation has proved injectivity. -/
theorem fundamental_scalar_involution (hp : Odd P.prime)
    (hk : Function.Injective (fundamentalHom D)) :
    fundamentalHom D (-1) ≠ 1 ∧ fundamentalHom D (-1) ^ 2 = 1 := by
  have hp2 : P.prime ≠ 2 := by
    intro h
    exact (by decide : ¬ Odd 2) (h ▸ hp)
  exact Matrix.SpecialLinearGroup.map_neg_one_isInvolution hp2 (fundamentalHom D) hk

end CFSG.Quasithin.ChapterA.Section02.OddLie.ExceptionalStructure.TrialityCentralizer
