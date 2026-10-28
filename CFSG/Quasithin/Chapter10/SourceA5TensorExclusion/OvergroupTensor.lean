module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupCore
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorOmegaCenterFree
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorLine
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SylowStabilizer
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldCartanOrbit

/-!
# Original tensor input to the overgroup core

The non-FF tensor action places the Thompson subgroup inside the local join's
2-core, so it is unchanged on passing to the component stabilizer. The original
omega-center bound and a nontrivial cubic Cartan action then put the tensor line
in the new overgroup's 2-core and kill its center. The cubic irreducibility uses
the actual four-element line, not an independent module identification.

Source: Aschbacher–Smith, 9.2.7 and 9.3.6.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

include D in
private theorem join_core_le_stabilizer :
    (localJoin T L).pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  have hEq : localJoin T L = L ⊔ (T : Subgroup G) := componentOrbit_sup L T
  rw [hEq]
  exact Chapter1.Section02.local_join_twoCore_le_sylow_stabilizer D.maximal.1

include m in
theorem thompson_stabilizer_eq :
    Stellmacher.elementaryAbelianMaxJ ((T : Subgroup G) ⊓ normalizer (L : Set G)) =
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) := by
  have hJcore : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      (localJoin T L).pCoreIn 2 := by
    rw [←D.sylow_centralizer_module (source_module_nonsolvable_uniqueness D),m.module_eq]
    exact le_inf (sSup_le fun _ hA => hA.1) m.thompson_centralizes_fullModule
  exact Stellmacher.elementaryAbelianMaxJ_eq_of_intermediate _ _
    (hJcore.trans (join_core_le_stabilizer (D := D))) inf_le_left

theorem omegaCenter_stabilizer_le_tensorLine
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤ D.fullModule) :
    omegaCenterIn ((T : Subgroup G) ⊓ normalizer (L : Set G)) ≤ m.tensorLine := by
  rw [m.omegaCenter_eq_fullModule_inf_of_outside_of_commutator_le hout hcomm _ (join_core_le_stabilizer (D := D)) inf_le_left]
  exact inf_le_inf_left _ (centralizer_le (le_inf inf_le_left
    (inf_le_right.trans (source_nonnormal_orbit_le_normalizer D hn))))

theorem tensorLine_fixed_eq_bot_of_cubic
    (A : Subgroup G) (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (d : G) (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdC : d ∉ centralizer (m.tensorLine : Set G)) :
    m.tensorLine ⊓ centralizer (A : Set G) = ⊥ := by
  apply (m.tensorLine_cartan_irreducible A hAU d hdA hd3 hdC _ inf_le_left
    ((le_inf hAU (A.le_normalizer.trans (normalizer_le_normalizer_centralizer A))).trans
      inf_normalizer_le_normalizer_inf)).resolve_right
  intro he
  apply hdC
  intro u hu
  exact ((show u ∈ m.tensorLine ⊓ centralizer (A : Set G) from he.symm ▸ hu).2 d hdA).symm

theorem outside_core_and_center_of_original_tensor_cubic
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2), localOrbit T L⁆ ≤ D.fullModule)
    (H A : Subgroup G) (hcore : pCore 2 H ≠ ⊥)
    (hLH : L ≤ H) (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hout : ¬ H ≤ D.maximalLocal)
    (hAH : A ≤ H) (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (d : G) (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdC : d ∉ centralizer (m.tensorLine : Set G)) :
    m.tensorLine ≤ H.pCoreIn 2 ∧ H ∈ Chapter1.He G ∧
      generalizedFitting H = pCore 2 H ∧ center H = ⊥ := by
  obtain ⟨z,hz,hzU,hzc⟩ := m.exists_central_involution_tensorLine
  exact source_a5_outside_characteristicTwo_of_irreducible_tensor_line D e hn H m.tensorLine A
    hcore hLH hRH hout (m.omegaCenter_stabilizer_le_tensorLine hn houtside hcomm)
    hAH hAU (m.tensorLine_cartan_irreducible A hAU d hdA hd3 hdC)
    (m.tensorLine_fixed_eq_bot_of_cubic A hAU d hdA hd3 hdC)
    m.sylow_centralizer_tensorPlane_le_stabilizer z hz hzU hzc
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
