module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Generation.Reduction
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The odd-linear and sporadic residual-generation sieve

This is the assembly interface for the last paragraph of the proof of
Aschbacher--Smith, Lemma 16.4.8 (printed pp.1187--1188).  The earlier table
calculation has to provide one odd prime `p` of rank greater than one in `L`,
a relative normal two-subgroup `Q` of `Lᵣ`, a simple quotient `Lᵣ / Q`, and
the divisibility of its order by `p`.  The reduction in `Generation.Reduction`
then proves that the displayed prime-to-`p` residual generates all of `Lᵣ`.

The table output is deliberately an input here.  This keeps the fixed groups
in the quotient distinct from images of fixed groups in a central cover, and
keeps normality relative to `Lᵣ`; no splitting of an extension is inferred.
The constructors retain `L₃(3)`, every Fermat/Mersenne parameter admitted by
(E2), and all nine sporadic names allowed by (E2)(iii), together with their
central covers.  The forbidden outer rows are not constructors: in
particular, the `M₂₂` row with quotient centralizer `Sz(2)/E₁₆` from 16.4.7
must be removed by its own exact exclusion before a table row is supplied.

No numbered source theorem is claimed by the existence of a table row.  The
model owners remain responsible for proving the row and the exclusions.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.OtherPreliminaries

variable {G : Type*} [Group G]

/-- The primitive output needed from one row of the 16.1.5 table.

`Q.Normal` is normality in the residual subgroup `D`, and the simple quotient
is the quotient of `D` itself.  Thus the row can be instantiated for a
nonsplit central extension without replacing a quotient fixed group by the
image of a fixed subgroup upstairs.
-/
structure ResidualGenerationRow (L D : Subgroup G) where
  p : ℕ
  prime : p.Prime
  odd : Odd p
  rank : 1 < primeRank p L
  Q : Subgroup D
  normal : Q.Normal
  two : IsPGroup 2 Q
  simple : IsSimpleGroup (D ⧸ Q)
  divides : p ∣ Nat.card (D ⧸ Q)

/-- A row supplies an index for `rankResidualSpan`. -/
theorem ResidualGenerationRow.mem_residualPrimes {L D : Subgroup G}
    (hrow : ResidualGenerationRow L D) : hrow.p ∈ residualPrimes L := by
  exact ⟨hrow.prime, hrow.odd, hrow.rank⟩

/-- The three exact model branches of the odd-linear/sporadic table.

The `pslTwo` constructor does not impose a lower bound on the parameter:
small Fermat/Mersenne overlaps are retained, as in (E2).  The sporadic
constructor uses the quotient by `pCore 2 L`, so it also covers the permitted
central covers.  The prime and quotient fields are the actual table output,
not a stronger residual-generation conclusion.
-/
inductive OtherSieveTableOutput (L D : Subgroup G) : Prop
  | pslThree (hmodel : ClassicalGroup.IsPSL L 3 3)
      (row : ResidualGenerationRow L D)
  | pslTwo (p : ℕ) (hprime : IsFermatOrMersennePrime p)
      (hmodel : ClassicalGroup.IsPSL L 2 p)
      (row : ResidualGenerationRow L D) (hrow : row.p = p)
  | sporadic (name : ClassificationModels.SporadicName)
      (hname : name ≠ .j3 ∧ name ≠ .he)
      (hmodel : Nonempty ((L ⧸ pCore 2 L) ≃* name.Carrier))
      (row : ResidualGenerationRow L D)

/-- Every table output has exactly one of the alternatives in (E2)(ii)--(iii).

This direction is useful to consumers that keep the source catalogue as a
separate premise.  The converse is intentionally absent: the table
calculation is an additional obligation.
-/
theorem OtherSieveTableOutput.isOtherEvenTypeComponent
    {L D : Subgroup G} (hout : OtherSieveTableOutput L D) :
    IsOtherEvenTypeComponent L := by
  cases hout with
  | pslThree hmodel _ => exact Or.inl hmodel
  | pslTwo p hprime hmodel _ _ => exact Or.inr (Or.inl ⟨p, hprime, hmodel⟩)
  | sporadic name hname hmodel _ =>
    exact Or.inr (Or.inr ⟨name, hname.1, hname.2, hmodel⟩)

/-- A simple-quotient row generates an arbitrary residual subgroup once its
two-perfectness is available. -/
theorem rankResidualSpan_eq_of_generation_row [Finite G]
    {L D : Subgroup G} (hD : IsPPerfect 2 D)
    (hrow : ResidualGenerationRow L D) :
    rankResidualSpan L D = D := by
  let _ : hrow.Q.Normal := hrow.normal
  let _ : IsSimpleGroup (D ⧸ hrow.Q) := hrow.simple
  exact rankResidualSpan_eq_of_simple_quotient
    hrow.mem_residualPrimes hrow.Q hrow.two hD hrow.divides

/-- The row interface specialized to the actual two-residual. -/
theorem involutionResidual_rankSpan_eq_of_generation_row [Finite G]
    {L : Subgroup G} {r : G}
    (hrow : ResidualGenerationRow L (involutionResidual L r)) :
    rankResidualSpan L (involutionResidual L r) = involutionResidual L r := by
  let _ : hrow.Q.Normal := hrow.normal
  let _ : IsSimpleGroup (involutionResidual L r ⧸ hrow.Q) := hrow.simple
  exact involutionResidual_rankSpan_eq_of_simple_quotient
    hrow.mem_residualPrimes hrow.Q hrow.two hrow.divides

/-- The requested residual-generation equality for the actual `Lᵣ`.

The hypotheses `hG`, `h`, `hr`, `hr2`, and `hL` retain the source context:
Hypothesis 16.1.1, the intersection setup, an involution of `R`, and the
odd-linear/sporadic component catalogue.  The only model-specific premise is
the exact table output `hout`; all residual two-perfectness is inherited from
the proved `Generation.Reduction` interface.
-/
theorem involutionResidual_rankResidualSpan_eq_of_other_sieve [Finite G]
    {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (_hG : Hypothesis1611 CFSG.KnownSimple.IsKnownSimple G)
    (_h : IntersectionSetup T z L g R) (_hr : r ∈ R) (_hr2 : orderOf r = 2)
    (_hL : IsOtherEvenTypeComponent L)
    (hout : OtherSieveTableOutput L (involutionResidual L r)) :
    rankResidualSpan L (involutionResidual L r) = involutionResidual L r := by
  cases hout with
  | pslThree _ hrow => exact involutionResidual_rankSpan_eq_of_generation_row hrow
  | pslTwo _ _ _ hrow _ => exact involutionResidual_rankSpan_eq_of_generation_row hrow
  | sporadic _ _ _ hrow => exact involutionResidual_rankSpan_eq_of_generation_row hrow

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual
