module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface

/-!
# Retaining the binary source models and their field parameters

The two positive binary alternatives of 1.1.5 retain simplicity, or the
nontrivial two-center with quotient PSL₃(4) or G₂(4). Each gives an actual
model of K*, transported through the canonical K/Z(K) equivalence. Small
derived models keep exponent one and Suzuki/Ree models keep the odd
field exponent. No small-field exclusion or innerness of E* is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3)(a,b), printed pp.501–503; proof of 13.6.6, printed p.927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve
open Chapter15.Section03.Candidates.ComponentStructure
open Chapter1.Section02.LocalModels ClassificationModels
universe u v

/-- Preserve the literal field parameter under an actual model isomorphism. -/
theorem BinaryModelAt.of_mulEquiv {Q : Type u} [Group Q] {R : Type v} [Group R]
    {m : ℕ} (h : BinaryModelAt Q m) (e : R ≃* Q) : BinaryModelAt R m := by
  cases h with
  | linear_two m hm hi => exact .linear_two m hm (hi.of_mulEquiv e)
  | unitary_three m hm hi => exact .unitary_three m hm (hi.of_mulEquiv e)
  | suzuki n hn hi => exact .suzuki n hn (hi.map fun i => e.trans i)
  | linear_three m hm hi => exact .linear_three m hm (hi.of_mulEquiv e)
  | symplectic m hm hi => exact .symplectic m hm (hi.of_mulEquiv e)
  | g2 m hm hi => exact .g2 m hm (hi.of_mulEquiv e)
  | triality m hm hi => exact .triality m hm (hi.of_mulEquiv e)
  | ree n hn hi =>
    obtain ⟨d, ⟨i⟩⟩ := hi
    exact .ree n hn ⟨d, ⟨e.trans i⟩⟩
  | symplectic_derived hi => exact .symplectic_derived (hi.map fun i => e.trans i)
  | g2_derived hi => exact .g2_derived (hi.map fun i => e.trans i)
  | tits hi => exact .tits (hi.map fun i => e.trans i)
  | binary_linear n hn hi => exact .binary_linear n hn (hi.of_mulEquiv e)

namespace ModelExclusions

/-- The two surviving source possibilities, with the full central-cover data. -/
inductive BinaryComponentModel (K : Type u) [Group K] : Prop
  | simple (hs : IsSimpleGroup K) (hm : LieTypeTwoModel K)
  | cover (hne : center K ≠ ⊥) (hc : center K = pCore 2 K)
      (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∨
        IsG2At (K ⧸ pCore 2 K) 4)

private theorem binary_parameter_of_lie {K : Type u} [Group K] (h : LieTypeTwoModel K) :
    ∃ m, 1 ≤ m ∧ BinaryModelAt K m := by
  rcases h with h | h | ⟨n, hn, hi⟩
  · cases h with
    | linear m hm hi => exact ⟨m, by omega, .linear_two m hm hi⟩
    | unitary m hm hi => exact ⟨m, by omega, .unitary_three m hm hi⟩
    | suzuki n hn hi => exact ⟨2 * n + 1, by omega, .suzuki n hn hi⟩
  · cases h with
    | linear m hm hi => exact ⟨m, hm, .linear_three m hm hi⟩
    | symplectic m hm hi => exact ⟨m, by omega, .symplectic m hm hi⟩
    | g2 m hm hi => exact ⟨m, by omega, .g2 m hm hi⟩
    | triality m hm hi => exact ⟨m, hm, .triality m hm hi⟩
    | ree n hn hi => exact ⟨2 * n + 1, by omega, .ree n hn hi⟩
    | symplectic_derived hi => exact ⟨1, le_rfl, .symplectic_derived hi⟩
    | g2_derived hi => exact ⟨1, le_rfl, .g2_derived hi⟩
    | tits hi => exact ⟨1, le_rfl, .tits hi⟩
  · exact ⟨1, le_rfl, .binary_linear n hn hi⟩

/-- Identify the actual component image with a positive-parameter binary model. -/
theorem component_binary_parameter {H : Type u} [Group H] (K : Subgroup H)
    (hK : IsComponent H K) (h : BinaryComponentModel K) :
    ∃ m, 1 ≤ m ∧ BinaryModelAt (NormalizerAction.componentImage K) m := by
  let : IsQuasisimple K := hK.2
  cases h with
  | simple hs hm =>
    let := hs
    have hc : center K = ⊥ := by
      rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with hc | hc
      · exact hc
      · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp hc)).elim
    let e := (NormalizerAction.componentCentralQuotientEquiv K).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)
    obtain ⟨m, hm, hi⟩ := binary_parameter_of_lie hm
    exact ⟨m, hm, hi.of_mulEquiv e⟩
  | cover _ hc hm =>
    let e := (NormalizerAction.componentCentralQuotientEquiv K).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hc)
    refine ⟨2, by decide, ?_⟩
    rcases hm with hm | hm
    · exact .linear_three 2 (by decide) (hm.of_mulEquiv e)
    · exact .g2 2 (by decide) (hm.of_mulEquiv e)

end ModelExclusions
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve
