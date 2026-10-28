module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.D14Source
public import CFSG.Quasithin.ChapterD.Section01.SourceSolvable

/-!
# Source 15.4.2 using the proved solvable D.1 alternatives

The H-star local in the actual ratio argument is already solvable by A/C.
Apply the complete solvable qrc theorem on the same V and its faithful
conjugation image. Its unique-factor outcome has the proved D.1.4 Sylow
alternative, which earlier 3.1.1 excludes. The other outcomes give the ratio
bound directly or through the original dual action. The outside-core route
and actual Xi-minus construction then supply all four source clauses.

Neither a universal D.1.5 assertion outside the solvable domain nor an
additional local conclusion is assumed. Universal A/C, earlier 3.1.1 and
solvable E.2.9 remain with their original producers.
Source: Aschbacher--Smith D.1.4--5, pp.175--177, and 15.4.2, pp.1155--1156.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource
open InsideCore MaximalPrimeSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M₀ M : Subgroup G} {V : Subgroup M₀}

/-- The actual inside-core local is solvable, so the complete proved solvable
D.1 alternatives discharge both earlier D.1 inputs. -/
theorem LocalHypotheses.cubicRatio_le_two_of_inside_core_source
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : Earlier311 (G := G))
    (l : LocalHypotheses T M₀ M V) (h : SourceHypotheses T)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hin : V.map M₀.subtype ≤ H.pCoreIn 2) :
    letI := l.reduced.normal
    letI := l.reduced.elementary
    cubicRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set M₀)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
  let := l.reduced.normal
  let := l.reduced.elementary
  let := IsElementaryAbelian.map (p := 2) (A := V) M₀.subtype
  let d := l.qrc hH
  have hn := l.module_ne_bot h h311
  have hdual : IsFFModule (imageRepresentation M₀ (V.map M₀.subtype) l.normalizes).dual →
      cubicRatio (Representation.NormalElementaryQuotient.representation V
        (QuotientGroup.mk' (centralizer (V : Set M₀)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 := by
    intro hf
    exact cubicRatio_le_two_of_dualFF hA hC T h M₀ l.mem_H V l.reduced
      (l.dualFF_of_image hf)
  have hsol := solvable_of_mem_HOver hA hC T h hH.1.1
  rcases ChapterD.UniqueFactor.source_solvable_qrc_cases d hn hsol with
    hout | hq | hf | hmultiple | hunique
  · exact (hout hin).elim
  · exact (cubicRatio_le_quadraticRatio _).trans
      (l.quadraticRatio_le_two_of_image (hq.1.trans (by norm_num)))
  · exact hdual hf
  · exact (cubicRatio_le_quadraticRatio _).trans
      (l.quadraticRatio_le_two_of_image hmultiple.1)
  · rcases ChapterD.UniqueFactor.source_dualFF_or_sylow d hin hunique.1 hsol with hf | hs
    · exact hdual hf
    · exact (l.not_core_sylow h h311 hH hs).elim

/-- The complete local source implication, on intrinsic V and the literal
faithful quotient M₀/C_M₀(V). The two branches use the same selected H. -/
theorem LocalHypotheses.cubicRatio_le_two_source
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : Earlier311 (G := G))
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
  · exact l.cubicRatio_le_two_of_inside_core_source hA hC h311 h hH hin
  · exact OutsideWitness.cubicRatio_le_two hA hC source_earlierB685 h29 h l hH hin

/-- The literal universal 15.4.2(4) input consumed by Xi-minus and the
maximal-prime proof. No chosen configuration or ratio bound is a premise. -/
theorem source_earlier1542Four_of_solvable_source
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : Earlier311 (G := G))
    (h29 : OutsideWitness.EarlierE29Solvable.{u}) :
    MaximalPrimeFive.Earlier1542Four (G := G) := by
  intro T h M₀ M hM₀ hM hle huniq V hV
  let := hV.normal
  let := hV.elementary
  dsimp only
  intro hkernel hcore
  exact LocalHypotheses.cubicRatio_le_two_source hA hC h311 h29
    ⟨hM₀, hM, hle, huniq, hV, hkernel, hcore⟩ h

/-- All four original source clauses with the D.1 and B.6.8(5) inputs proved. -/
theorem source_lemma_15_4_2_of_solvable_source
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h311 : Earlier311 (G := G))
    (h29 : OutsideWitness.EarlierE29Solvable.{u}) :
    Earlier1542 (G := G) ∧ MaximalPrimeFive.Earlier1542Four (G := G) := by
  have h44 := source_earlier1542Four_of_solvable_source hA hC h311 h29
  exact ⟨InitialSource.XiMinus.source_earlier1542 hA hC h44,h44⟩

end CFSG.Quasithin.Chapter15.Section04.RatioSource
