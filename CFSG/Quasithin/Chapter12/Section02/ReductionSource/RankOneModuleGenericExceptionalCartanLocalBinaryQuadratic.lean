module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryQuadratic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Quadratic action on the retained Frattini layer for the original chosen module

The original omega-span and its retained kernel span normalize one another.
Their commutator is in the exact kernel, and the seven-moved part centralizes
the omega-span. Its conjugation action on the retained Frattini quotient is
quadratic, fixes the seed image, and has order at most four; E lies in its
full kernel. The original chosen module, Sylow, Hall subgroups and quotient
maps are unchanged. This supplies action constraints, not the missing
large-span exclusion or the full local Cartan conclusion.

Source: Aschbacher--Smith 5.1.13 and 12.2.2, printed pp.635--638,795,
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

/-- Apply the retained-kernel action reduction to the original chosen module. -/
theorem rankOne_local_cartan_binary_triality_kernel_mutual_action
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
    N ≤ normalizer (U : Set G) ∧ U ≤ normalizer (N : Set G) ∧
      ⁅N,U⁆ ≤ E ∧ ⁅⁅N,U⁆,U⁆ = ⊥ ∧ ⁅N,B⁆ ≤ centralizer (U : Set G) :=
  BinaryOmega.original_binary_triality_kernel_mutual_action
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

/-- Apply the retained-kernel action reduction to the original chosen module. -/
theorem rankOne_local_cartan_binary_triality_kernel_quadratic_frattini
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
    ∃ a : U →* MulAut N,
      (∀ (u : U) (v : N), ((a u v : N) : G) =
        (u : G) * (v : G) * (u : G)⁻¹) ∧
      let d := (quotientAut (frattini N)).comp a
      let q := QuotientGroup.mk' (frattini N)
      let V := (E.subgroupOf N).map q
      (∀ (u : U) (v : N ⧸ frattini N), d u v * v⁻¹ ∈ V) ∧
      (∀ (u : U) (v : V), d u v = v) ∧
      (∀ (u w : U) (v : N ⧸ frattini N),
        d u (d w v * v⁻¹) = d w v * v⁻¹) ∧
      E.subgroupOf U ≤ d.ker ∧ Nat.card d.range ≤ 4 ∧
      Nat.card V ≤ 256 ∧ 2^24 ≤ Nat.card (N ⧸ frattini N) :=
  BinaryOmega.original_binary_triality_kernel_quadratic_frattini
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
