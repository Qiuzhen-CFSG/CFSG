module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.LocalNormalizer
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.ComponentSection

/-!
# Larger defining fields: local preparation and terminal assembly

The local normalizer has theta of three-rank one, and the component
subspace is the literal image of U₀ = [U_H,⟨L^T⟩] in U_H/Z. The terminal
assembly applies the natural SL₂ calculation to the component closure
itself. Its relative normality and equality L₀ = [L₀,Y₀] follow from (i)
and the replacement; no equality L₀ = L upstairs is needed for this step.
The actual SL₂ equivalence forces the star image to be nontrivial.

The remaining obligations are the four Lie-type alternatives, their
Borel and normalizer analysis, the best-offender selection of the natural
module with compatible coordinates, and the legitimate B.2.14 application.
The conditional terminal theorem below is not the larger-field exclusion.
Final source assembly remains in this module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49 between (k) and (l), printed p.1144.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields
variable {G : Type*} [Group G]

variable (Z : Subgroup G)

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
open scoped MatrixGroups

omit [CharP F 2] [Algebra (ZMod 2) F] in
private theorem subgroup_ne_bot_of_sl2_equiv (A : Subgroup G) (e : A ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    A ≠ ⊥ := by
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (Matrix.SpecialLinearGroup.upperUnipotentHom_injective F).nontrivial
  exact (A.nontrivial_iff_ne_bot).mp e.surjective.nontrivial

/-- Terminal assembly on the actual component closure. The cubic actor,
relative normality, nontrivial star image and seed centralization are derived.
The model coordinates, their Borel marking and the B.2.14 decomposition must
still be supplied by the larger-field reduction. -/
theorem no_natural_componentSection
    (H M ZS L Y0 T V : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hgen : H = reducedOvergroup L Y0 T)
    (hcomm : L = ⁅L, Y0⁆) (hTY : T ≤ normalizer (Y0 : Set G))
    (hθ : theta (M ⊓ H) = Y0)
    (hθV : theta (M ⊓ centralizer (V : Set G)) = Y0)
    (hZSV : ZS ≤ V) (hZSH : ZS ≤ H) (hYL0 : Y0 ≤ localSpan L T)
    (hsplit : localSpan ZS H = ⁅localSpan ZS H, localSpan L T⁆ ⊔
      commutatorPreimage (localSpan ZS H) H Z)
    (sectionModel : Representation.SL2CubicFixedSection.NaturalComponentSection
      (F := F) action.representation (starImage H (localSpan L T))
        (componentSection Z H ZS L T))
    (hB : ∀ y : starImage H Y0,
      sectionModel.model ⟨y, (map_mono (comap_mono hYL0)) y.property⟩ ∈
        Matrix.SpecialLinearGroup.rankOneBorel F) : False := by
  have hL0H : localSpan L T ≤ H := hgen ▸ le_sup_left
  have hn := componentClosure_normal_in_replacement L Y0 T
    (le_normalizer_iff_commutator_le_left.mpr hcomm.ge) hTY
  rw [← hgen] at hn
  have hnormal := (normal_subgroupOf_iff_le_normalizer hL0H).mp hn
  have hcent : Y0 ≤ centralizer (ZS : Set G) :=
    ((hθV ▸ theta_le _).trans inf_le_right).trans (centralizer_le hZSV)
  exact no_natural_section_of_component_action H M ZS Z (localSpan L T) Y0 action
    hZSH hL0H hnormal hθ (componentClosure_commutator L Y0 T hcomm hTY)
    (subgroup_ne_bot_of_sl2_equiv _ sectionModel.model) (componentSection Z H ZS L T)
    (componentSection_split_of_commutatorPreimage Z H ZS L T action
      (conjugateSpanBy_le_self hZSH) hL0H hsplit) sectionModel hYL0 hB hcent
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields
