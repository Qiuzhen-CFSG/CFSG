module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinarySmallInvariant
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Retained binary-kernel growth for the original chosen module

The original chosen-module input gives the upper bound 256 for its
omega-span and the lower bound 4096 for O₂(CT). The CT-span of the exact
kernel U ∩ O₂(CT) either has order at least 4096 or equals that kernel.
In the small branch a quintic in the original seven-centralizer residual
moves the kernel, and U is not contained in O₂(CT). All maps, both Hall
conditions and the containing component are those of the original input.

These are the literal chosen-module applications of the kernel analysis;
the binary-triality exclusion and exceptional witness remain to be proved.
Source: Aschbacher--Smith 5.1.10--13 and 12.2.2, printed pp.634--638,795,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B K Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The original chosen input makes every component-invariant subgroup of the omega-span centralized by that component. -/
theorem rankOne_local_cartan_binary_triality_small_invariant
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    Nat.card U ≤ 256 ∧
      ∀ N : Subgroup G, N ≤ U → C.map Y.subtype ≤ normalizer (N : Set G) →
        C.map Y.subtype ≤ centralizer (N : Set G) :=
  BinaryOmega.original_binary_triality_small_invariant
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

/-- The original containing two-core has order at least 4096. -/
theorem rankOne_local_cartan_binary_triality_core_size
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    4096 ≤ Nat.card ((C.map Y.subtype ⊔ (T : Subgroup G)).pCoreIn 2) :=
  BinaryOmega.original_binary_triality_core_size
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

/-- The original kernel has either a large CT-span or a quintic displacement inside the seven-centralizer residual. -/
theorem rankOne_local_cartan_binary_triality_kernel_growth
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let E := U ⊓ X.pCoreIn 2
    let N := conjugateSpanBy E X
    N ≤ X.pCoreIn 2 ∧ X ≤ normalizer (N : Set G) ∧
      (C.map Y.subtype ≤ normalizer (E : Set G) ↔
        C.map Y.subtype ≤ centralizer (E : Set G)) ∧
      ((N = E ∧ C.map Y.subtype ≤ centralizer (E : Set G) ∧ Nat.card N ≤ 256 ∧
        ¬ U ≤ X.pCoreIn 2 ∧
        ∃ F : Subgroup G, F ≤ residual (L ⊓ centralizer (B : Set G)) ∧
          Nat.card F = 5 ∧ F ≤ centralizer (B : Set G) ∧
          ¬ F ≤ normalizer (E : Set G)) ∨ 4096 ≤ Nat.card N) :=
  BinaryOmega.original_binary_triality_kernel_growth
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
