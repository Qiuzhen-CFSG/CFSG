module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.Splitting

/-!
# The seed decomposition on the literal central quotient

Apply the universal B.2.14 splitting clause to H/Z, with the image of the
original ambient Sylow subgroup and the image of Z_S. The faithful
SectionAction and the elementary normal U_H prove the characteristic-two
condition for this quotient. The seed is central in its Sylow subgroup by
15.3.48(2); its trivial-image case is handled directly. Containment (k) and
H = L₀Y₀T then identify the full moved subspace with [U_H,L₀].

The output is the sum of the literal component section and the fixed space
in U_H/Z. No direct-sum assertion is made. The unused assumption F*(H) =
O₂(H) in the older Splitting adapter is unnecessary here.

The only new local premises are Z_S ≤ T and [Z_S,T] ≤ Z, the seed placement
and centrality in 15.3.48(2). B.2.14 itself remains an explicit universal
input for the source assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.13–14,
printed p.78, and proof of 15.3.49 preceding (k), printed p.1144.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
open Subgroup Representation.BinaryOffender
open ComponentReduction ModelReduction LargerFields LargerFields.Splitting
open CFSG.Quasithin.Chapter15.Section03
open scoped IsMulCommutative

universe u
namespace Input
variable {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E L upper : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)
include d

/-- B.2.14 applies to the actual H/Z: its characteristic-two condition
follows from the faithful SectionAction and the elementary normal U_H/Z. -/
theorem component_section_split
    (source : CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry.SourceB214Splitting.{u})
    (hcontainment : Y0 ≤ localSpan L T) (hZST : ZS ≤ T) (h48 : ⁅ZS, T⁆ ≤ Z) :
    componentSection Z H ZS L T ⊔ fixedSpace d.placed.action.representation ⊤ = ⊤ := by
  let _ : (Z.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer d.placed.action.normalizes_layer
  have hZSH : ZS ≤ H := hZST.trans d.t_le
  have hUH : localSpan ZS H ≤ H := conjugateSpanBy_le_self hZSH
  have hcommU : ⁅localSpan ZS H, localSpan L T⁆ ≤ localSpan ZS H :=
    le_normalizer_iff_commutator_le_left.mp
      (d.closure_le.trans d.placed.action.normalizes)
  apply componentSection_split_of_commutatorPreimage Z H ZS L T d.placed.action
    hUH d.closure_le
  by_cases hseed : ZS ≤ Z
  · have hUZ : localSpan ZS H ≤ Z :=
      conjugateSpanBy_le hseed d.placed.action.normalizes_layer
    apply le_antisymm
    · exact (le_commutatorPreimage le_rfl
        ((commutator_mono hUZ le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp d.placed.action.normalizes_layer))).trans
        le_sup_right
    · exact sup_le hcommU (commutatorPreimage_le _ _ _)
  obtain ⟨P, hP⟩ := d.sylowIn
  let Pbar := P.mapSurjective (QuotientGroup.mk'_surjective (Z.subgroupOf H))
  have hb := source (H ⧸ Z.subgroupOf H)
    (quotient_characteristicTwo H Z (localSpan ZS H) d.placed.action hUH) Pbar
    (tildeImage H Z ZS) (tildeImage_ne_bot H Z ZS hZSH hseed)
    (seed_le_tilde_sylow_omega H Z ZS T (localSpan ZS H)
      (le_conjugateSpanBy ZS H) hZST d.t_le P hP h48)
  change normalClosure (tildeImage H Z ZS : Set (H ⧸ Z.subgroupOf H)) = _ at hb
  rw [← tildeImage_span H Z ZS hZSH,
    full_commutator_image_eq_component H Z ZS L Y0 T d.replacement
      d.component.commutator_eq d.normalizes hcontainment hZST h48] at hb
  exact (tilde_split_iff H Z (localSpan ZS H) ⁅localSpan ZS H, localSpan L T⁆ hUH
    hcommU d.placed.action.layer_le d.placed.action.normalizes_layer).mp hb

end Input
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels
