module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At.Setup
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At.Module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.LocalConstructionSupplement.Commutator
public import CFSG.Quasithin.Chapter10.SourceThompsonControl
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality

/-!
# The original omega module and plane from local source inputs

The multiple-overgroup guard gives the outside maximal subgroup used in
Thompson movement. B.5.1 identifies the moved omega module with the chosen V;
the vanishing first cohomology calculation then supplies its fixed supplement.
The actual marked action constructs the invariant plane, its nonfixed vector,
and the local Sylow subgroup of the vector centralizer inside N_G(L).

All structural and module inputs concern the original G,T. The omega product
contains the whole V. Ambient Sylow promotion remains a separate residual
calculation; it is not included in the constructed LocalGeometry.

Source: Aschbacher–Smith, 12.4.5 and the start of 12.4.6, pp.813–814.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

/-- Thompson movement on the chosen module with the original overgroup guard. -/
theorem thompson_moves_chosen
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple
    h.simpleQTKE T h.maximal_faithful.1
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have hout := Chapter3.hasMaximalOutside_of_many T hmany
    (normalizer (L : Set G)) hm (structural L h).1
  have hTV := ((structural L h).2.2 V D).1
  have hMV := ((structural L h).2.2 V D).2.2.2.resolve_right hne
  let F := D.fundamentalSetup h.toHypothesis1221
  have hm : F.moduleSubgroup = V := by
    rw [D.fundamentalSetup_module]
    exact le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTV)
      (le_componentOrbit _ _)
  have hf : F.fullModule = V := by
    rw [D.fundamentalSetup_fullModule]
    exact le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hMV)
      (le_componentOrbit _ _)
  intro hJ
  have hout' : Chapter3.HasMaximalOutside T F.maximalLocal := by
    simpa only [Chapter3.Section02.FundamentalSetup.maximalLocal, D.localOrbit_eq] using hout
  have he := Chapter10.source_fullModule_fixed_eq_bot_of_centralizes
    F hout' (hm.symm ▸ hJ)
  rw [hf, D.localOrbit_eq] at he
  exact hne he

/-- Movement persists on the literal omega center of C_T(V). -/
theorem thompson_moves_omega_center
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) : Set G) :=
  fun hJ => thompson_moves_chosen h D hmany structural hne
    (hJ.trans (centralizer_le (chosen_le_omega_center D)))

/-- B.5.1 on the original omega module, with its movement premise discharged. -/
theorem omega_commutator_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    ⁅omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)), L⁆ = V := by
  obtain ⟨E⟩ := extension_of_modules h D modules hmodel hne
  exact omega_commutator_eq_of_thompson_movement D h E
    ((structural L h).2.2 V D).1 hne
    (thompson_moves_omega_center h D hmany structural hne)

/-- The fixed supplement contains the whole original chosen module. -/
theorem fixed_supplement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) :
    omegaCenterIn ((T : Subgroup G) ⊓ centralizer (V : Set G)) =
      (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊔ V := by
  obtain ⟨E⟩ := extension_of_modules h D modules hmodel hne
  exact fixed_supplement_of_commutator_le D E h ((structural L h).2.2 V D).1
    hne (omega_commutator_eq h D hmany structural modules hmodel hne).le

/-- Construct the actual plane and local Sylow witness with no geometry callback. -/
theorem local_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥) : Nonempty (LocalGeometry D) := by
  obtain ⟨ext⟩ := extension_of_modules h D modules hmodel hne
  have hTL := (structural L h).1
  have hTV := ((structural L h).2.2 V D).1
  have hMV := ((structural L h).2.2 V D).2.2.2.resolve_right hne
  obtain ⟨E, hEV, hEc, hTE⟩ := exists_invariant_plane ext hne hTV
  obtain ⟨v, hvE, hvF, hi, hSyl⟩ :=
    invariant_plane_local_sylow ext hne hTL hMV E hEV hEc hTE
  exact ⟨⟨E, hEV, hEc, v, hvE, hvF,
    fixed_supplement h D hmany structural modules hmodel hne,
    invariant_plane_fixed_space ext hne hTL E hEV hEc hi, hi, hSyl⟩⟩

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.At
