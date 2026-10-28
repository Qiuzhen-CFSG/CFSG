module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.SmallSymplectic
public import Theory.SpecificGroups.ClassicalOrthogonal.RankOneComparison.Comparison

/-!
# Small orthogonal quotients in the classical FF branch

Conjugation of SL₂ on trace-zero matrices identifies the literal elementary
orthogonal group in dimension three with PSL₂. Its scalar subgroup is trivial,
so the comparison descends through CFSG's actual projective quotient. This
works over every field, hence in particular for all permitted odd parameters.
The exact catalogue parameters transfer to the linear branch. At field orders
5, 7 and 9 the existing concrete PSL₂ comparisons give the quotient alternative.

These are the rank-one comparison and its applications in the classical
quotient step of Aschbacher–Smith B.1.13, printed pp.73–74. The low-rank
orthogonal conventions are those of GLS3 §2.7. The separate comparisons
PΩ₅(3) ≃ PSp₄(3), PΩ₄⁻(3) ≃ PSL₂(9), and PSp₄(3) ≃ PSU₄(2) remain
necessary for the other surviving small cases; none is assumed here.
-/

public section

open Subgroup

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal

universe u
variable {L : Type u} [Group L]

/-- The actual rank-one odd orthogonal scalar quotient is PSL₂, over the same field. -/
theorem isPSL_of_isPOmegaOdd_rankOne {S : Type u} [Group S] {q : ℕ}
    (h : ClassicalGroup.IsPOmegaOdd S 1 q) : ClassicalGroup.IsPSL S 2 q := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc,
    ⟨e.trans ClassicalOrthogonal.RankOneComparison.projectiveEquivPSL⟩⟩

/-- The retained orthogonal rank-one parameters satisfy precisely the linear
rank-two conditions needed by the linear recognition owner. -/
theorem linearParameters_of_orthogonalOdd_rankOne {q : ℕ}
    (hp : KnownSimple.OrthogonalOddParameters 1 q) : KnownSimple.LinearParameters 2 q :=
  ⟨hp.1, by decide, fun _ => hp.2.2.1 rfl⟩

/-- Apply linear quotient recognition to the literal odd orthogonal rank-one
branch, transferring both its field and its catalogue parameters. -/
theorem quotientAlternative_of_odd_rankOne_of_linear {q : ℕ}
    (hp : KnownSimple.OrthogonalOddParameters 1 q)
    (h : ClassicalGroup.IsPOmegaOdd (L ⧸ center L) 1 q)
    (hlinear : KnownSimple.LinearParameters 2 q →
      ClassicalGroup.IsPSL (L ⧸ center L) 2 q → QuotientAlternative L) :
    QuotientAlternative L :=
  hlinear (linearParameters_of_orthogonalOdd_rankOne hp) (isPSL_of_isPOmegaOdd_rankOne h)

/-- The three small odd rank-one orthogonal quotients are A₅, PSL₃(2), A₆
through the actual PSL₂ carrier comparisons. -/
theorem quotientAlternative_of_odd_rankOne_small {q : ℕ}
    (h : ClassicalGroup.IsPOmegaOdd (L ⧸ center L) 1 q)
    (hq : q = 5 ∨ q = 7 ∨ q = 9) : QuotientAlternative L :=
  quotientAlternative_of_psl2_small (isPSL_of_isPOmegaOdd_rankOne h) hq

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal
