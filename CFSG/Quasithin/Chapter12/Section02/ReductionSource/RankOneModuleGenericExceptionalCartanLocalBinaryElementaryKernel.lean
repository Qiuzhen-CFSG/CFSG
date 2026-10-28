module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryElementaryKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The elementary retained kernel for the original chosen module

The same original omega-span has one or two A₅ modules and a literal
CT/O₂(CT) image of order at most four. Its exact kernel has order at least
four in the single-copy case and at least 64 in the double-copy case.
This applies the binary elementary calculation to the actual chosen-module
input, retaining both Hall conditions and every original quotient map.
It does not yet exclude binary triality or construct the exceptional witness.

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

/-- The actual elementary quotient image has order at most four. -/
theorem rankOne_local_cartan_binary_triality_elementary_image_bound
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
    Nonempty ((X ⧸ pCore 2 X) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) ∧
      Nat.card ((U.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) ≤ 4 :=
  BinaryOmega.original_binary_triality_elementary_image_bound
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

/-- The original omega-span has one or two copies, with the exact retained-kernel bounds. -/
theorem rankOne_local_cartan_binary_triality_elementary_kernel_bound
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
    IsOneOrTwoA5Modules L U ∧
      Nat.card ((U.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) ≤ 4 ∧
      Nat.card U ≤ 4 * Nat.card E ∧
      ((Nat.card U = 16 ∧ 4 ≤ Nat.card E) ∨
        (Nat.card U = 256 ∧ 64 ≤ Nat.card E)) :=
  BinaryOmega.original_binary_triality_elementary_kernel_bound
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
