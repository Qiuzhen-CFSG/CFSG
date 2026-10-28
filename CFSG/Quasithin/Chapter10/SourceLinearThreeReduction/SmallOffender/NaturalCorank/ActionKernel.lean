module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.MovedSize
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking.FactorKernel

/-!
# The action kernel on the original natural three-space section

The supplied SL₃(2) marking identifies the kernel on W/C_W(L) with O₂(L),
where W=[V,L]. Since O₂(L) centralizes V and W=[W,L], the three-subgroups
lemma gives the same action kernel on W and on its central quotient for
every simultaneous normalizer of L and W. In particular, an element of M
stabilizing W and fixing V/Wᵗ centralizes W. The possibly nonzero central
fixed subgroup is retained throughout.

This is the quotient-kernel step in Aschbacher--Smith 10.2.12, printed
p.754. Only the model-independent stabilizer and full-module lemmas are
reused from the A₅ development; the action kernel is proved here from the
literal natural SL₃(2) section.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (m : SourceLinearThreeGeometry T D)

include m

/-- The original component has exactly its two-core as section-action kernel. -/
theorem moved_quotient_kernel :
    commutatorPreimage L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) = L.pCoreIn 2 := by
  let q := m.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Injective (Representation.specialLinearNatural (k := ZMod 2) 3) := by
    intro a b hab
    exact Matrix.SpecialLinearGroup.toLin'_injective
      (LinearEquiv.toLinearMap_injective hab)
  have hn : L ≤ normalizer
      ((⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) : Subgroup G) : Set G) :=
    (le_inf L.le_normalizer (normalizer_commutator_ge_right _ _)).trans
      (source_original_moved_fixed_normalizer D)
  have he := m.natural.action_kernel_map hn
  change (((Representation.specialLinearNatural 3).comp q).ker).map L.subtype = _ at he
  rw [MonoidHom.ker_comp_of_injective q (Representation.specialLinearNatural 3) hf,
    MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (pCore 2 L))
      m.quotient.toMonoidHom m.quotient.injective, QuotientGroup.ker_mk'] at he
  exact he.symm

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
    rw [moved_quotient_kernel m]
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

/-- Fixing the natural head forces fixation of the entire original moved factor. -/
theorem moved_fixed_kernel_element {b : G}
    (hbL : b ∈ normalizer (L : Set G))
    (hbW : b ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hcomm : ⁅zpowers b,⁅D.fullModule,L⁆⁆ ≤
      ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)) :
    b ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  have hH : zpowers b ≤ normalizer (L : Set G) ⊓
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := zpowers_le.mpr ⟨hbL,hbW⟩
  have hb := le_commutatorPreimage hH hcomm (mem_zpowers b)
  rw [moved_normalizer_quotient_kernel m] at hb
  exact hb.2

/-- The literal source application C_M(V/Wᵗ) ∩ N_M(W) ≤ C_M(W). -/
theorem partner_quotient_kernel_element
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    {b : G} (hbM : b ∈ D.maximalLocal)
    (hbW : b ∈ normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hcomm : ⁅zpowers b,D.fullModule⁆ ≤
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) :
    b ∈ centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  apply moved_fixed_kernel_element m
    (source_original_moved_stabilizer_le_component_normalizer D ht htn
      (m.crossed t ht htn) ⟨hbM,hbW⟩) hbW
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  exact le_inf (le_normalizer_iff_commutator_le_right.mp (zpowers_le.mpr hbW))
    (((commutator_mono le_rfl hWV).trans hcomm).trans (m.crossed t ht htn))

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
