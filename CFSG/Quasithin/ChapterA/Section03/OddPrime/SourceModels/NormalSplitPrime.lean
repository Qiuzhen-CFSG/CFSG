module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Binary
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Covers
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.Exclusions
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.OddTernary

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CatalogueSieve
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CubicSieve
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.MixedLinear
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.FieldSieve
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.UnitarySieve
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverSieve
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverOuter

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ExceptionalSplit
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ExceptionalQuadratic
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ExceptionalCyclotomic
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ReeField

/-!
# Checked branches of normal split-prime A.3.18

The original normal split-extension hypotheses give an actual ordinary
component through the two-core quotient. The marked binary rank-two branch
now proves the full source Alternatives proposition, including its ambient
star residual model. Outside that branch, the genuine full Theorem C catalogue
and the outer-two and alternating-cover exclusions are derived on the original
intrinsic quotient. The completed A.3.6 theorem separates the actual ordinary
component into centerless and genuine central three-cover cases.
The odd-prime ternary rows with p-prime center now also give the complete
projective alternative, with the actual PGL or PGU star residual. The cubic
binary linear row now has the full PGL star residual for every p-prime center.
The fixed-subfield exclusions and the Mathieu-cover exponent calculation give
`alternatives_or_actor_remainder`: noncubic even-characteristic actors,
odd-degree binary unitary cubics, or genuine classical cubic covers remain.
The mixed linear circle is also excluded under a marked equivalence of the
literal star pair, using its proved twisted-norm nonsplitting.
The full symplectic and noncubic G₂ fixed-subfield exclusions, together with
binary linear absorption and cyclic-Sylow bounds, now yield
`alternatives_or_reduced_actor_remainder`: only noncubic unitary, triality
and Ree actors, cubic unitary actors, and classical cubic covers remain.
The subsequent `alternatives_or_exceptional_or_cover` removes every unitary
row: noncubic absorption and the full cubic PGU₃ star-residual calculation
leave only noncubic triality/Ree actors and classical cubic covers.
The `alternatives_or_cover_action` refinement excludes inner actors on every
linear cubic cover. An inner unitary actor retains its actual order-nine
implementer, nonidentity central cube, and centralizer rank bound.
The `alternatives_or_outer_cover` refinement now excludes those inner unitary
actors as well, using their actual fixed rank-two torus. Only exceptional
noncubic field actors and outer actors on central cubic covers remain.
The `alternatives_or_nonsplit_or_cover` refinement excludes primes dividing
q - 1 in both exceptional families by constructing elementary rank-two
subgroups fixed by the actual coefficient actor. The further
`alternatives_or_refined_nonsplit_or_cover` excludes all quadratic triality
primes, including those dividing q + 1. Its remaining triality primes divide
the original exponent and one of the third or sixth cyclotomic factors.

`alternatives_or_remaining` records this partial source reduction honestly:
`Remaining` must still be eliminated before obtaining the universal normal
split-prime theorem. In particular it does not discard the odd-characteristic,
other Lie, sporadic or nontrivial p-center cases. The complete projective and
split-diagonal alternatives in SourceModels are unchanged.
Source: Aschbacher–Smith A.3.18, printed pp.51–53; ordinary-root consumer
4.3.6, printed p.615.
The fixed-subfield cyclotomic construction now removes all remaining triality
actors in `alternatives_or_ree_or_cover`, retaining only nonsplit Ree actors
and the genuine outer central cubic-cover clauses.
The fixed-subfield Ree construction now excludes every remaining noncubic
actor in `alternatives_or_outer_cubic_cover`. The original outside prime
must be three (`prime_eq_three`); the central cubic-cover diagonal clauses
are the sole remaining source branch.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02.LocalModels
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
variable {H : Type*} [Group H] [Finite H]

/-- The still-open source cases, expressed on the actual intrinsic quotient.
This record does not assert any of the unproved source alternatives. -/
structure Remaining (p : ℕ) (K : Subgroup H) : Prop where
  nonbinary : ¬ BinaryModel (K ⧸ pCore 2 K) p
  catalogue : Section02.IsTheoremCModel
    ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K))
  center_cases : center (twoCoreComponent K) = ⊥ ∨
    (Nonempty (center (twoCoreComponent K) ≃* Multiplicative (ZMod 3)) ∧
      ThreeCoverModel (twoCoreComponent K))
  outer : Nat.Coprime p (Nat.card (center (K ⧸ pCore 2 K))) →
    ¬ IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K))
  alternating : p = 3 → ∀ n : ℕ, 6 ≤ n → ¬ IsAlternating (K ⧸ pCore 2 K) n
  covers : p = 3 → ¬ (IsAlternatingCover (K ⧸ pCore 2 K) 6 ∨
    IsAlternatingCover (K ⧸ pCore 2 K) 7)

/-- Checked progress on the original full split domain. The binary branch
has the exact source conclusion; every other branch retains the full catalogue
and the proved actor exclusions. Eliminating `Remaining` is still required. -/
theorem alternatives_or_remaining
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    {K : Subgroup H} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : H) (ha : orderOf a = p) (haK : a ∉ K) (hgen : K ⊔ zpowers a = ⊤) :
    Alternatives p K ∨ Remaining p K := by
  classical
  by_cases hm : BinaryModel (K ⧸ pCore 2 K) p
  · exact Or.inl (alternatives_of_binary_model hH hK hp ho hr hm a ha haK hgen)
  by_cases ht : OddTernaryModel (K ⧸ pCore 2 K) p
  · exact Or.inl (alternatives_of_odd_ternary_model hH hK hp ho hr ht a ha haK hgen)
  · refine Or.inr ⟨hm, ?_, twoCore_center_cases hH hK, ?_, ?_, ?_⟩
    · exact (twoCore_central_quotient_model hH hK).of_mulEquiv
        (centralQuotientEquiv (twoCoreComponentEquiv hK).symm)
    · intro hz
      exact outer_not_twoGroup hH hK hp ho hr hz a ha haK
    · intro hp3 n hn
      exact not_alternating_model hH hK hn a (ha.trans hp3) haK
    · intro hp3
      exact not_alternating_cover hH hK a (ha.trans hp3) haK

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
