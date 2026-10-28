module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.ReducedModule
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus

/-!
# The Xi ratio application with reducedness discharged

Apply the original 15.4.2(4) ratio bound to the actual commutator module,
using its proved reducedness. The literal Sylow-centralizer equality remains
the independent kernel producer's obligation. The genuine universal A/C
inputs and the separate source assertion 15.4.2(4) are unchanged.

Source: Aschbacher--Smith, Lemma 3.2.13, printed pp.584--585, specialized
to the empty-family application by 15.4.2(4), printed pp.1155--1156.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original ratio bound requires only the remaining exact Sylow kernel;
reducedness of the original module is supplied internally. -/
theorem source_cubicRatio_of_kernel
    (hA : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple K)
    (hC : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple K)
    (T : Sylow 2 G) (h : SourceHypotheses T)
    (h44 : MaximalPrimeFive.Earlier1542Four (G := G))
    {X : Subgroup G} (hX : X ∈ Chapter1.Xi G (T : Subgroup G))
    (hkernel : (T : Subgroup G).subgroupOf (sourceGroup (T : Subgroup G) X) ⊓
      centralizer (sourceModule (T : Subgroup G) X : Set (sourceGroup (T : Subgroup G) X)) =
        pCore 2 (sourceGroup (T : Subgroup G) X)) :
    let V := sourceModule (T : Subgroup G) X
    let := (sourceModule_reduced T hX).normal
    cubicRatio (Representation.NormalElementaryQuotient.representation V
      (QuotientGroup.mk' (centralizer (V : Set (sourceGroup (T : Subgroup G) X))))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) ≤ 2 :=
  source_cubicRatio_of_reduced_kernel hA hC T h h44 hX (sourceModule_reduced T hX) hkernel

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
