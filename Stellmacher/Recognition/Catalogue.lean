module

public import ABG.Basic
public import Theory.Comparator.Defs
public import Theory.SpecificGroups.Tits.Presentation

/-!
# Actual models in the simple N and N2 classifications

The N catalogue lists PSL2, Suzuki, A7, M11, PSL3(3), PSU3(3), and the
Tits group. Every constructor carries an actual group isomorphism. PSL2
has separate even-field and odd-field constructors to use the concrete
field models of Bender--Suzuki and Gorenstein--Walter, with the solvable
small parameters excluded. The N2 catalogue adds PSU3 over even fields.
Membership asserts only an isomorphism to a listed model; it includes no
local configuration or unproved recognition theorem.

Sources: Kurzweil--Stellmacher, Appendix p.370; GLS1 (28.1); Thompson VI
p.573 for the Tits correction. The Tits model is Parrott's ten-generator,
37-relator presentation (1972, p.683). Finiteness, simplicity, and recognition
of that presentation are separate mathematical obligations.
-/

namespace Stellmacher
universe u

/-- Actual models in Thompson's nonsolvable simple N-group classification. -/
public inductive IsNGroupModel (G : Type u) [Group G] : Prop
  | psl2Even (n : ℕ) (hn : 2 ≤ n) (e : G ≃* PSL2Model n)
  | psl2Odd (K : Type u) [Field K] [Finite K]
      (hodd : Odd (Nat.card K)) (hcard : 3 < Nat.card K)
      (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
  | suzuki (n : ℕ) (hn : 1 ≤ n) (e : G ≃* SzModel n)
  | alternatingSeven (e : G ≃* alternatingGroup (Fin 7))
  | mathieuEleven (e : G ≃* Sporadic.Mathieu.M11)
  | linearThree (h : ABG.IsPSL3 G 3)
  | unitaryThree (h : ABG.IsPSU3 G 3)
  | tits (e : G ≃* Tits.ParrottGroup)

/-- The generalized N2 catalogue adds the even-field unitary rank-one family. -/
@[expose] public def IsNTwoGroupModel (G : Type u) [Group G] : Prop :=
  IsNGroupModel G ∨ ∃ n : ℕ, 2 ≤ n ∧ Nonempty (G ≃* PSU3Model n)

end Stellmacher
