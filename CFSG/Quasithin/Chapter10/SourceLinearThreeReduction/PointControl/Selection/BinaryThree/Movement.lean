module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.PairActor
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.CoreOmega
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SharpExtension
public import CFSG.Quasithin.Chapter3.Section02.ThompsonCommutator

/-!
# The original binary-three omega movement bound

Write Ω = Ω₁Z(O₂(L₀T)). The selected full module V lies in Ω and has
Sylow centralizer O₂(L₀T). Every maximum elementary A of T lies in T₁,
whose faithful action on V has no strong offenders. The common kernel
on V fixes Ω, so the maximum elementary counting argument gives
Ω = C_Ω(A)V. Thus J(T) acts trivially on Ω/V, and the original identity
L₀ = [L₀,J(T)] gives [Ω,L₀] ≤ V.

The earlier central-cover splitting and residual calculation then prove
all positive-kernel point geometry, including PointSylowControl on the
original opposite vectors with only conditional half-Sylow uniqueness.
No module-choice, zero-kernel normalizer, or rank-one conclusion is asserted.
Source: Aschbacher--Smith, the FF step of 10.2.8 and its application in
10.2.9, printed pp.749--750; maximum elementary counting is B.2.4.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem full_le_core_omega (hfull : D.fullModule = D.moduleSubgroup) :
    D.fullModule ≤ omegaCenterIn ((localJoin T L).pCoreIn 2) := by
  rw [hfull]
  let := D.module_elementary
  intro v hv
  exact (mem_omegaCenterIn_iff _ _).mpr ⟨D.module_le_core hv,
    fun q hq => (D.core_centralizes_module hq v hv).symm,
    elemPow_eq_one_of_isElementaryAbelian v hv⟩

/-- Every maximum elementary subgroup supplies the original Ω/V fixed supplement. -/
theorem maximal_elementary_core_omega_supplement
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {A : Subgroup G} (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G)) :
    omegaCenterIn ((localJoin T L).pCoreIn 2) =
      (omegaCenterIn ((localJoin T L).pCoreIn 2) ⊓ centralizer (A : Set G)) ⊔ D.fullModule := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  let Ω := omegaCenterIn ((localJoin T L).pCoreIn 2)
  let : IsElementaryAbelian 2 Ω := inferInstance
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hSN : S ≤ normalizer (D.fullModule : Set G) :=
    (inf_le_left.trans (le_normalizer_componentOrbit L T)).trans D.maximalLocal_normalizes_fullModule
  have hQT : (localJoin T L).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (localJoin T L) (T.subtype le_sup_right)
  have hΩT : Ω ≤ (T : Subgroup G) := fun z hz => hQT ((mem_omegaCenterIn_iff _ _).mp hz).1
  apply ChapterD.UniqueFactor.maxElementary_supplement_of_image_not_strong
    (T : Subgroup G) S D.fullModule Ω A hSN
    (le_inf hA.1 ((le_sSup hA).trans D.thompson_normalizes_component))
    (full_le_core_omega D hfull) hΩT hA
  · intro a ha z hz
    have haQ : a ∈ (localJoin T L).pCoreIn 2 := by
      rw [←D.sylow_centralizer_module hu,←hfull]
      exact ⟨hA.1 ha.1,ha.2⟩
    exact ((mem_omegaCenterIn_iff _ _).mp hz).2.1 a haQ |>.symm
  · exact half_sylow_full_not_strong D hmodel hne ht htn hcross

/-- The source FF movement bound is proved on the actual local two-core. -/
theorem core_omega_orbit_movement_le
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),localOrbit T L⁆ ≤ D.fullModule := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  let Ω := omegaCenterIn ((localJoin T L).pCoreIn 2)
  let : IsElementaryAbelian 2 Ω := inferInstance
  have hVN : localJoin T L ≤ normalizer (D.fullModule : Set G) := by
    rw [hfull]
    exact D.join_normalizes_module
  have hΩV : Ω ≤ normalizer (D.fullModule : Set G) :=
    (Ω.le_centralizer.trans (centralizer_le (full_le_core_omega D hfull))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hΩJ := thompson_commutator_le_of_max_fixed_supplements (T : Subgroup G)
    D.fullModule Ω (le_sup_right.trans hVN) hΩV
    (fun A hA => maximal_elementary_core_omega_supplement D hmodel hne hfull ht htn hcross hA)
  exact actor_commutator_le_of_thompson_generation (localJoin T L) (localOrbit T L)
    (T : Subgroup G) D.fullModule Ω le_sup_left le_sup_right hVN (join_normalizes_core_omega (T := T) (L := L))
    (D.actor_eq_commutator_of_thompson_not_centralizes hu (hfull ▸ hJ)) hΩJ

/-- The positive-kernel binary-three geometry has no remaining omega-movement
premise. Every point is still measured in the original opposite factor. -/
theorem positive_kernel_point_geometry
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    BinaryThreePointGeometry D t := by
  refine ⟨fixed_layer_centralizes_half_sylow D hmodel ht htn hcross,?_⟩
  intro v hv _ hv0 _
  exact point_case_of_core_omega_commutator_le D hmodel hne hfull
    (fun hn => htn (hn ht))
    (core_omega_component_movement_le_of_orbit_movement_le D
      (core_omega_orbit_movement_le D hmodel hne hfull hJ ht htn hcross))
    (partner_le_fullModule D ht hv) (hcross hv) hv0

/-- The original point-control contract in the positive-kernel row, including
initially fixed vectors, with only the permitted half-Sylow uniqueness input. -/
theorem positive_kernel_pointSylowControl
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (hhalf : HalfSylowUnique D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    PointSylowControl D t :=
  pointSylowControl_of_core_omega_orbit_movement_le D hmodel hne hfull
    (core_omega_orbit_movement_le D hmodel hne hfull hJ ht htn hcross) hhalf ht htn hcross

end CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
