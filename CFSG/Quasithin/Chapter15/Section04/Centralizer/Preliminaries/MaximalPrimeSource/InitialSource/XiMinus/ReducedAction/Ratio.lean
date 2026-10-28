module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.ReducedAction
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.ReducedModule.Ratio

/-!
# The Xi ratio bound with the module kernels discharged

Apply the source ratio theorem to V=[R₂(XT),X]. Reducedness is already
proved, and ReducedAction supplies the exact Sylow kernel from V≠1.
The genuine universal A/C and separate 15.4.2(4) inputs are retained.
Source: Aschbacher--Smith, Lemma 3.2.13, printed pp.584--585, specialized by
15.4.2(4), printed pp.1155--1156.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual source ratio application has no unresolved module-kernel premise. -/
theorem source_cubicRatio_of_nontrivial
    (hA : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple K)
    (hC : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple K)
    (T : Sylow 2 G) (h : SourceHypotheses T)
    (h44 : MaximalPrimeFive.Earlier1542Four (G := G))
    {X : Subgroup G} (hX : X ∈ Chapter1.Xi G (T : Subgroup G))
    (hne : sourceModule (T : Subgroup G) X ≠ ⊥) :
    let V := sourceModule (T : Subgroup G) X
    let := (sourceModule_reduced T hX).normal
    cubicRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set (sourceGroup (T : Subgroup G) X))))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 :=
  source_cubicRatio_of_kernel hA hC T h h44 hX
    (source_sylow_centralizer_eq_core T hX hne)

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
