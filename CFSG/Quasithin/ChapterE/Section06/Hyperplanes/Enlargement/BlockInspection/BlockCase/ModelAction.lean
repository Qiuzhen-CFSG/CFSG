module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.FixedSpace
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.FactorType
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.ModelAction.FactorWitness
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.ModelAction.SylowAction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.ModelAction.FactorIdentification

/-!
# Natural-block identification and common-Sylow action

For an actual block X in C_G(A), E.6.5 restricts the common Sylow Q to
any characteristic-two intermediate group containing Q and X. The intrinsic
block-action theorem then realizes every v in V by an element of the first
omega subgroup of the center of the actual Sylow intersection X ∩ Q.
Transport to X retains the literal conjugation formula in G.

CharacteristicTwo constructs the required intermediate group ⟨X,Q⟩, even
when Q does not normalize X. FactorIdentification identifies the actual X
with an E.6.7 factor. FixedSpace gives C_V(X) = A and FactorType forces
the natural SL₂(4) module, distinct from the A₅ deleted permutation module.

The final assembly discharges ProperBlockFactors and retains only the
permitted exact E.6.7, C.1.9 and E.6.21 inputs under Hypothesis E.6.1.
It proves the requested model and action without needing Hypothesis E.6.15.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7,
printed p.246, and E.6.23, printed p.254 (PDF pp.257 and 265).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
variable {G : Type*} [Group G] [Finite G]
variable {𝒦 : GroupClass} {T : Sylow 2 G} {M V A X J : Subgroup G}

open InvariantSubspaces.BlockSelection

/-- Identification with an E.6.7 factor completes both the natural-module
recognition and its literal common-Sylow action. -/
theorem naturalOvergroup_of_factor [IsElementaryAbelian 2 V]
    (h : HypothesisE61 𝒦 T M V) (h19 : BlockCommutationInput G) (h21 : OddCoreFree V)
    {U L : Subgroup G} (hU : U ∈ obstructionFamily M V) (hUh : IsHyperplane V U)
    (hA : A ∈ obstructionFamily M V) (hAU : A ≤ U) (hc : subgroupCorank V A = 2)
    (hL : SmallBlock U L) (he : ¬ L ≤ M) (hLX : L < X) (hX : CentralizerBlock A X)
    (d : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V A J)
    (i : Fin d.count) (hi : d.block i = X) :
    NaturalOvergroup (sylowCentralizer (T : Subgroup G) V) V X := by
  have hf := proper_block_fixedSpace h h19 h21 hU hUh hAU hc hL he hLX hX
  have hn := factor_naturalFour_of_corank_two d hc i (by rw [hi, hf]; exact hc)
  rw [hi] at hn
  exact ⟨hn, block_common_sylow_action h h21 hA hX⟩

/-- Conditional assembly: the only remaining premise is the identification
of each actual proper overgroup with an E.6.7 factor. -/
theorem properOvergroupModels_of_factors
    (h : HypothesisE61 𝒦 T M V) (h19 : BlockCommutationInput G) (h21 : OddCoreFree V)
    (hfactors : ProperBlockFactors T M V) : ProperOvergroupModels T M V := by
  let _ := h.elementary
  intro U hU hUh L hL he A hA hAU hc X hLX hX htype
  obtain ⟨d, i, hi⟩ := hfactors U hU hUh L hL he A hA hAU hc X hLX hX htype
    (block_join_characteristicTwo h h21 hA hX)
  exact naturalOvergroup_of_factor h h19 h21 hU hUh hA hAU hc hL he hLX hX d i hi

/-- The actual proper block is natural of type L₂(4), with its common Sylow
intersection and literal omega-center action. Factor identification and
characteristic two are proved; only the exact earlier-source inputs remain. -/
theorem properOvergroupModels_of_e67
    (h : HypothesisE61 𝒦 T M V) (h67 : E67Input T M V)
    (h19 : BlockCommutationInput G) (h21 : OddCoreFree V) :
    ProperOvergroupModels T M V :=
  properOvergroupModels_of_factors h h19 h21 (properBlockFactors_of_e67 h h67 h19 h21)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
