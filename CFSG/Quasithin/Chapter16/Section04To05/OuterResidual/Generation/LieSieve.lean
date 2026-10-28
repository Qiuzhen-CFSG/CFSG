module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Generation.Reduction
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Generation.Field

/-!
# The characteristic-two Lie sieve

This file is the small assembly point for the ordinary branch of 16.4.8.  The
table lemmas in 16.1.2--16.1.6 and the intersection lemmas in 16.4.2--16.4.5
are deliberately inputs here: this module only performs the residual
generation deduction which is used by the source proof.

For a nontrivial residual, a table row supplies an odd prime of rank greater
than one, a normal two-subgroup of the residual, and a simple quotient whose
order is divisible by that prime.  `Reduction` turns precisely those data into
the equality `Λ(Lᵣ) = Lᵣ`.  The other possible output is the genuine field
action on the component.  It is represented by an isomorphism of the actual
component with `PSL₂(2ⁿ)` intertwining conjugation with a nonidentity field
involution; it is not merely a label for the isomorphism type of a fixed
subgroup.

The small identifications `PSL₂(4) ≅ PSL₂(5)`, `PSL₃(2) ≅ PSL₂(7)` and
`Sp₄(2)' ≅ PSL₂(9)`, the `q = 9`/`S₆` row, and the permitted central covers
remain table data.  In particular, the corrected `PSL₅(2)` residual row is
not replaced by the false elementary-cubic extension from the printed table.
Those model-specific facts are consumed by constructing one of the explicit
alternatives below; no family tag is used as a substitute for a residual or
an action witness.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, Lemma
16.4.8, printed p.1188, with the tables on pp.1170--1172.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual

open Subgroup Theory.GroupTheory

universe u

variable {G : Type u} [Group G] [Finite G]

/-! A source-correct package for the single odd-prime row used by `Λ`. -/

/-- The part of a characteristic-two table row which is needed for residual
generation.  The fields are the actual subgroup and quotient statements; in
particular, this is not a proposition asserting that the residual is already
generated. -/
structure SimpleResidualRow (L D : Subgroup G) where
  p : ℕ
  hp : p ∈ residualPrimes L
  Q : Subgroup D
  normal : Q.Normal
  simple : IsSimpleGroup (D ⧸ Q)
  twoCore : IsPGroup 2 Q
  quotient_dvd : p ∣ Nat.card (D ⧸ Q)

/-- The three mathematically distinct outputs of the source table inspection:
an odd-prime row, a trivial two-residual (the small rank-one rows), or the
actual binary field action. -/
inductive LieSieveAlternative (L D : Subgroup G) (a : MulAut L) : Prop
  | prime (row : SimpleResidualRow L D) : LieSieveAlternative L D a
  | trivial (hD : D = ⊥) : LieSieveAlternative L D a
  | binaryField (hfield : IsBinaryFieldInvolution a) : LieSieveAlternative L D a

/-! Elementary assembly lemmas. -/

omit [Finite G] in
theorem rankResidualSpan_eq_of_trivial_residual {L D : Subgroup G}
    (hD : D = ⊥) : rankResidualSpan L D = D := by
  subst D
  exact le_antisymm (rankResidualSpan_le L ⊥) bot_le

theorem rankResidualSpan_eq_of_simpleResidualRow {L D : Subgroup G}
    (hPerfect : IsPPerfect 2 D) (row : SimpleResidualRow L D) :
    rankResidualSpan L D = D := by
  exact @rankResidualSpan_eq_of_simple_quotient _ _ _ L D row.p row.hp row.Q
    row.normal row.simple row.twoCore hPerfect row.quotient_dvd

/-!
The source-facing sieve theorem.  `h1611`, `hLie`, and `h` are retained in the
statement because they are the standing hypotheses under which the table rows
are obtained.  The proof uses only the exact row outputs and does not turn any
of those records into an implicit classification theorem.
-/

theorem rankResidualSpan_eq_or_binaryField_of_table
    {K : GroupClass.{u}} {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (_h1611 : Hypothesis1611 K G)
    (h : IntersectionSetup T z L g R)
    (_hLie : IsEvenTypeLieComponent L)
    (hr : r ∈ R)
    (hrow : LieSieveAlternative L (involutionResidual L r)
      (involutionAction h hr)) :
    rankResidualSpan L (involutionResidual L r) = involutionResidual L r ∨
      IsBinaryFieldInvolution (involutionAction h hr) := by
  rcases hrow with row | hD | hfield
  · exact Or.inl (@involutionResidual_rankSpan_eq_of_simple_quotient _ _ _ L r row.p
      row.hp row.Q row.normal row.simple row.twoCore row.quotient_dvd)
  · exact Or.inl (rankResidualSpan_eq_of_trivial_residual hD)
  · exact Or.inr hfield

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual
