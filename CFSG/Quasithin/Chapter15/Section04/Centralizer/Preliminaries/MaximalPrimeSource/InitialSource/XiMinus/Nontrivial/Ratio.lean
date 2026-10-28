module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.Nontrivial
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.ReducedAction.Ratio

/-!
# The Xi ratio bound with all module hypotheses proved

Faithful Xi membership now supplies nontriviality of the original module
V=[R₂(XT),X]. Its reducedness and exact kernels are already proved, so the
source ratio bound requires only the genuine universal A/C and independent
15.4.2(4) inputs. The canonical five-factor argument remains a separate step.
Source: Aschbacher--Smith, 3.2.13, printed pp.584--585, using 15.4.2(4).
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original faithful Xi ratio application has no additional module premise. -/
theorem source_cubicRatio_of_mem_XiF
    (hA : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple K)
    (hC : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple K)
    (T : Sylow 2 G) (h : SourceHypotheses T)
    (h44 : MaximalPrimeFive.Earlier1542Four (G := G))
    {X : Subgroup G} (hX : X ∈ Chapter1.XiF G (T : Subgroup G)) :
    let V := sourceModule (T : Subgroup G) X
    let := (sourceModule_reduced T hX.1).normal
    cubicRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set (sourceGroup (T : Subgroup G) X))))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 :=
  source_cubicRatio_of_nontrivial hA hC T h h44 hX.1
    (sourceModule_ne_bot_of_mem_XiF hX)

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
