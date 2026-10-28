module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinaryIdentification
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.QuotientAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.AlternatingSix
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.LinearModels
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.Tits
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.UnitarySuzukiSymplectic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.Exceptional

/-!
# Binary branches of the initial component sieve

Exhaust the genuine binary component models using their concrete Sylow-fixer
geometry. Every surviving field branch has exponent greater than one and
contains the literal E* in K*. The derived symplectic branch identifies the
whole quotient X* with S₆; the other small-field endpoints are excluded.

The application to BinaryComponentModel retains both simple components and
the nontrivial two-central covers of PSL₃(4) and G₂(4), via the canonical
K/Z(K) equivalence. Suzuki and Ree retain their exponent 2*n+1. All intrinsic
model premises are discharged by the imported branch theorems. The parent
source argument remains responsible for obtaining the positive alternatives
of 1.1.5(3) and the marked action data.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927, following
1.1.5(3)(a,b), printed pp.501–503.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
open A5Module
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

/-- Exhaust all twelve concrete binary constructors, including every small
derived endpoint, to obtain the field-or-whole-S₆ alternative. -/
theorem alternatives_of_binary_model_at (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {m : ℕ}
    (hm : BinaryModelAt (NormalizerAction.componentImage K) m) :
    ModelSieveAlternatives K a := by
  cases hm with
  | linear_two m hm hi => exact Or.inl (largeField_of_linear_two K hK a hm hi)
  | unitary_three m hm hi => exact Or.inl (largeField_of_unitary_three K hK a hm hi)
  | suzuki n hn hi => exact Or.inl (largeField_of_suzuki K hK a hn hi)
  | linear_three m hm hi => exact Or.inl (largeField_of_linear_three K hK a hm hi)
  | symplectic m hm hi => exact Or.inl (largeField_of_symplectic K hK a hm hi)
  | g2 m hm hi => exact Or.inl (largeField_of_g2 K hK a hm hi)
  | triality m hm hi => exact Or.inl (largeField_of_triality K hK a hm hi)
  | ree n hn hi => exact Or.inl (largeField_of_ree K hK a hn hi)
  | symplectic_derived hi => exact alternatives_of_symplectic_derived K hK a hi
  | g2_derived hi => exact (not_g2_derived K hK a hi).elim
  | tits hi => exact (not_tits K hK a hi).elim
  | binary_linear n hn hi => exact (not_binary_linear K hK a hn hi).elim

/-- The binary step in the source sieve: either a genuine larger defining
field with E* ≤ K*, or an isomorphism of the entire X* with S₆. The positive
1.1.5(3)(a,b) model input keeps the simple/central-cover distinction. -/
theorem alternatives_of_binary_component (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) (hm : BinaryComponentModel K) :
    ModelSieveAlternatives K a := by
  obtain ⟨m, _, hmodel⟩ := component_binary_parameter K hK hm
  exact alternatives_of_binary_model_at K hK a hmodel

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
