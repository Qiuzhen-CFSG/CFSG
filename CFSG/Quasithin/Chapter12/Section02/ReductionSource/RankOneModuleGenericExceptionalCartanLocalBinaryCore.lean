module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The binary-triality quotient kernel on the original chosen-module input

The original chosen input replaces its local overgroup by the join of the
same containing component with the same full Sylow. Escape persists, and
this join has actual binary-triality two-core quotient. The original
omega-span has quotient image of order at most eight; its literal core
intersection satisfies the exact kernel-image count and the resulting
lower bound. No zero-core or chosen-subgroup invariance premise is added.

This supplies the original 12.2.2 application of the local quantitative
core bound. It leaves the binary-triality exclusion and exceptional
component witness with the local Cartan classification owner.
Source: Aschbacher--Smith 5.1.10--13 and 12.2.2,
printed pp.634--638,795, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B K Y : Subgroup G}
  (a : ChosenModule T L V)
include a

/-- The chosen input retains the original escape, genuine quotient and
exact omega-span kernel in the smaller local overgroup. -/
theorem rankOne_local_cartan_binary_triality_core_bound
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
    let q := QuotientGroup.mk' (pCore 2 X)
    X ≤ Y ∧ X ∈ Chapter1.HOver G (H : Set G) ∧ A ≤ X ∧
      ¬ A ⊓ X ≤ normalizer (residual H : Set G) ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) ∧
      Nat.card ((U.subgroupOf X).map q) ≤ 8 ∧
      Nat.card (U ⊓ X.pCoreIn 2 : Subgroup G) *
        Nat.card ((U.subgroupOf X).map q) = Nat.card U ∧
      Nat.card U ≤ 8 * Nat.card (U ⊓ X.pCoreIn 2 : Subgroup G) ∧
      2 ≤ Nat.card (U ⊓ X.pCoreIn 2 : Subgroup G) :=
  BinaryOmega.original_binary_triality_core_bound
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
