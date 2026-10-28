module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.FixedSpaces.Inputs

/-!
# Transporting the component kernel to the whole stabilizer

The three-subgroups lemma transfers the original kernel on W/C_W(L) to
any simultaneous normalizer of L and W, because W=[W,L]. The two-factor
permutation then gives the literal partner-quotient application in M.
Only the component kernel is an input; no A₅ or natural-module marking
is used. Source: Aschbacher--Smith 10.2.12, printed p.754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (inputs : ActionInputs D)
include inputs

/-- No simultaneous normalizer has an action hidden in the central fixed part. -/
theorem moved_normalizer_quotient_kernel :
    commutatorPreimage
      (normalizer (L : Set G) ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
      ⁅D.fullModule,L⁆ (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) =
    (normalizer (L : Set G) ⊓ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G)) ⊓
      centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let H := normalizer (L : Set G) ⊓ normalizer (W : Set G)
  have hAH : L ≤ H := le_inf L.le_normalizer (normalizer_commutator_ge_right _ _)
  have hker : commutatorPreimage L W (W ⊓ centralizer (L : Set G)) ≤
      centralizer (W : Set G) := by
    rw [inputs.kernel]
    have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    exact (source_component_core_centralizes_fullModule D).trans (centralizer_le hWV)
  apply le_antisymm
  · exact le_inf (commutatorPreimage_le _ _ _)
      (commutatorPreimage_le_centralizer_of_fully_moved H L W
        (W ⊓ centralizer (L : Set G)) hAH inf_le_left inf_le_right
        (source_original_moved_fixed_normalizer D) inf_le_right
        (source_full_moved_eq_commutator D) hker)
  · apply le_commutatorPreimage inf_le_left
    exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le

/-- Fixing the central quotient forces fixation of the entire original moved factor. -/
theorem moved_fixed_kernel_element {b : G}
    (hbL : b ∈ normalizer (L : Set G))
    (hbW : b ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hcomm : ⁅zpowers b,⁅D.fullModule,L⁆⁆ ≤
      ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) :
    b ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have hH : zpowers b ≤ normalizer (L : Set G) ⊓
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := zpowers_le.mpr ⟨hbL,hbW⟩
  have hb := le_commutatorPreimage hH hcomm (mem_zpowers b)
  rw [moved_normalizer_quotient_kernel inputs] at hb
  exact hb.2

/-- The literal source application C_M(V/Wᵗ) ∩ N_M(W) ≤ C_M(W). -/
theorem partner_quotient_kernel_element
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {b : G} (hbM : b ∈ D.maximalLocal)
    (hbW : b ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hcomm : ⁅zpowers b,D.fullModule⁆ ≤
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) :
    b ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  apply moved_fixed_kernel_element inputs
    (source_original_moved_stabilizer_le_component_normalizer D ht htn
      hcross ⟨hbM,hbW⟩) hbW
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  exact le_inf (le_normalizer_iff_commutator_le_right.mp (zpowers_le.mpr hbW))
    (((commutator_mono le_rfl hWV).trans hcomm).trans hcross)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition.FixedSpaces
