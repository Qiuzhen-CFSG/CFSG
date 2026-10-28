module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinarySevenFrattini
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The seven-moved core and its original Frattini action

For the same P = [N,B] in the intersection of the two original cores,
B acts faithfully on P/Φ(P), with no nonidentity common fixed point.
This quotient has order 8^k for k > 0, and P intersect U lies in Φ(P),
whose ambient image lies in Φ(N). All quotient maps and both Hall
subgroups are those of the original chosen-module input.

This supplies the Frattini separation for the remaining ambient
core comparison. Binary-triality exclusion and the exceptional-component
sieve are still obligations of the original source theorem.
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

/-- The original chosen module supplies the same seven-moved Frattini section. -/
theorem rankOne_local_cartan_binary_triality_seven_moved_frattini
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
    let P := ⁅N,B⁆
    ⁅P,B⁆ = P ∧
      P ⊓ U ≤ (frattini P).map P.subtype ∧
      (frattini P).map P.subtype ≤ (frattini N).map N.subtype ∧
      ∃ a : B →* MulAut P,
        (∀ (b : B) (v : P), ((a b v : P) : G) =
          (b : G) * (v : G) * (b : G)⁻¹) ∧
        let d := (quotientAut (frattini P)).comp a
        (∀ v : P ⧸ frattini P, (∀ b : B, d b v = v) → v = 1) ∧
        Function.Injective d ∧
        ∃ k : ℕ, 0 < k ∧ Nat.card (P ⧸ frattini P) = 8^k :=
  BinaryOmega.original_binary_triality_seven_moved_frattini
    (a.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
