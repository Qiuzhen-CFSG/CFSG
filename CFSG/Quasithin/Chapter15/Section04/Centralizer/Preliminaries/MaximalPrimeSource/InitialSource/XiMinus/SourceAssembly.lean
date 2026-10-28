module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.SmallSupport.Completion
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.Nontrivial.Ratio

/-!
# The E-specific Xi-minus inclusion and its 15.4.2 consumer

For the actual faithful Xi members, reducedness, nontriviality, and the
original X-kernel containment are already proved. The independent
15.4.2(4) assertion supplies the original ratio bound. Applying the
completed prime and canonical-factor argument proves XiStarF ⊆ XiMinus
and hence the literal 15.4.2(1--3) source implication.

The genuine universal Theorems A and C and the separate 15.4.2(4) premise
remain explicit for the higher assembly. Clause (4) must be obtained from
clauses (1),(2) independently of clause (3); this argument does not assume
Earlier1542. No local kernel, factor, automizer, or Xi-minus premise remains.
Source: Aschbacher--Smith, 3.2.13, printed pp.584--585, applied in 15.4.2,
printed pp.1155--1156.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The E-specific source inclusion, with every original module and factor premise discharged. -/
theorem source_XiStarF_subset_XiMinus
    (hA : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple K)
    (hC : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple K)
    (h44 : MaximalPrimeFive.Earlier1542Four (G := G))
    (T : Sylow 2 G) (h : SourceHypotheses T) :
    Chapter1.XiStarF G (T : Subgroup G) ⊆ Chapter3.XiMinus G (T : Subgroup G) := by
  intro X hX
  exact source_mem_XiMinus_of_module_conditions T hX.1.1 (sourceModule_reduced T hX.1.1)
    ((sourceKernelInFrattini_iff hX.1.1).mpr
      (source_kernel_le_frattini hX.1.1 (sourceModule_ne_bot_of_mem_XiF hX.1)))
    (source_cubicRatio_of_mem_XiF hA hC T h h44 hX.1)

/-- The literal universal 15.4.2(1--3) consumer of the completed Xi-minus inclusion. -/
theorem source_earlier1542
    (hA : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple K)
    (hC : ∀ (K : Type u) [Group K] [Finite K],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple K)
    (h44 : MaximalPrimeFive.Earlier1542Four (G := G)) :
    Earlier1542 (G := G) :=
  TheoremCInputs.source_earlier1542 hA hC (source_XiStarF_subset_XiMinus hA hC h44)

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
