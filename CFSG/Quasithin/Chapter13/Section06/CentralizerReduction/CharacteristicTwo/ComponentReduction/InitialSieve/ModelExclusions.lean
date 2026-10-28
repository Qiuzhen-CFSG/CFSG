module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.Alternating
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.QuotientAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.SmallModels
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinaryIdentification

/-!
# Model exclusions in the initial component argument

The alternating alternatives, including their triple covers, are excluded
using the actual two-group outer quotients and the source residual. Thus z
acts by an inner automorphism. The central four-group acts faithfully on
the component's central quotient and fixes a Sylow subgroup there, excluding
PSL₃(3) and the M₁₁ two-core quotient by their concrete fixer bounds.

The positive binary interface retains both the simple and nontrivial-cover
possibilities and identifies a positive field parameter on the actual K*.
The remaining PSL₂ prime-field, sporadic and small/large-field calculations
are still needed to derive ModelSieveAlternatives. This module does not
assert that dichotomy yet.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3), printed pp.501–503; proof of 13.6.6, printed pp.926–927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions
open Subgroup Theory.GroupTheory A5Module
universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {κ : GroupClass.{u}} {T : Sylow 2 G} {s : Marking L V}

/-- Apply the full earlier source theorem and discharge its two outer alternatives. -/
theorem source_z_inner (d : Setup κ T s) (earlier : Earlier115Three κ G)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) :
    K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩ ∈ MulAut.innerSubgroup K :=
  z_inner_of_model_action d K hK hodd a (source_model_action d earlier K hK a)

/-- The source z-image lies in the actual embedded component quotient. -/
theorem source_zStar_mem_componentImage (d : Setup κ T s) (earlier : Earlier115Three κ G)
    (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) :
    NormalizerAction.quotient K ⟨zLocal s, a.z_normalizes⟩ ∈
      NormalizerAction.componentImage K :=
  (NormalizerAction.action_mem_inner_iff K _).mp (source_z_inner d earlier hodd K hK a)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions
