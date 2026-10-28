module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.InsideCore
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.OutsideWitness
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeFive

/-!
# The source cubic-ratio implication 15.4.2(4)

Universal A/C gives parts (1),(2), independently of Xi-minus. The literal
source assumptions then supply D.1.1, and genuine 3.1.1 excludes the
zero-module case and the residual-Sylow outcome. The dual-FF branch is
proved on the original faithful quotient. A two-conjugate witness likewise
gives the desired bound on that same quotient, with all actor maps retained.

Choose an actual H in H*(T,M) and split according to V ≤ O₂(H). The inside
branch applies the D.1 alternatives and excludes the residual-Sylow outcome;
the outside branch constructs the B.6/E.2 two-conjugate witness. Thus every
local premise in `Earlier1542Four` is discharged on its original quotient.

Only the genuine universal earlier A/C, D.1.4–5, B.6.8(5), solvable E.2.9,
and 3.1.1 implications remain explicit. Their source producers retain their
discharge; neither 15.4.2(3) nor an Xi-minus inclusion is used here.

Source: Aschbacher–Smith, 15.4.2(4), printed p.1156.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource
open MaximalPrimeSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The complete local source implication, on intrinsic V and the literal
faithful quotient M₀/C_M₀(V). The two branches use the same selected H. -/
theorem LocalHypotheses.cubicRatio_le_two
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : Earlier311 (G := G))
    (hD15 : InsideCore.EarlierD15.{u}) (hD14 : InsideCore.EarlierD14Sylow.{u})
    (h685 : OutsideWitness.EarlierB685.{u})
    (h29 : OutsideWitness.EarlierE29Solvable.{u})
    {T : Sylow 2 G} {M₀ M : Subgroup G} {V : Subgroup M₀}
    (l : LocalHypotheses T M₀ M V) (h : SourceHypotheses T) :
    letI := l.reduced.normal
    letI := l.reduced.elementary
    cubicRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set M₀)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
  obtain ⟨H, hH⟩ := exists_HStar h l.maximal
  by_cases hin : V.map M₀.subtype ≤ H.pCoreIn 2
  · exact l.cubicRatio_le_two_of_inside_core hA hC h311 hD15 hD14 h hH hin
  · exact OutsideWitness.cubicRatio_le_two hA hC h685 h29 h l hH hin

/-- The literal universal 15.4.2(4) input consumed by Xi-minus and the
maximal-prime proof. No chosen configuration or ratio bound is a premise. -/
theorem source_earlier1542Four
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : Earlier311 (G := G))
    (hD15 : InsideCore.EarlierD15.{u}) (hD14 : InsideCore.EarlierD14Sylow.{u})
    (h685 : OutsideWitness.EarlierB685.{u})
    (h29 : OutsideWitness.EarlierE29Solvable.{u}) :
    MaximalPrimeFive.Earlier1542Four (G := G) := by
  intro T h M₀ M hM₀ hM hle huniq V hV
  let := hV.normal
  let := hV.elementary
  dsimp only
  intro hkernel hcore
  exact LocalHypotheses.cubicRatio_le_two hA hC h311 hD15 hD14 h685 h29
    ⟨hM₀, hM, hle, huniq, hV, hkernel, hcore⟩ h

end CFSG.Quasithin.Chapter15.Section04.RatioSource
