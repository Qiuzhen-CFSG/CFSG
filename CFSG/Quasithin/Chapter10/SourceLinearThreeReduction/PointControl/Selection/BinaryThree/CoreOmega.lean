module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.Residual
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import Theory.Representation.FirstCohomologyAutomorphism.FixedSupplement
public import Theory.Representation.SLThreeCentralExtension.ChiefCohomology
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow

/-!
# Omega-center control in the positive binary-three row

The fourteen-vector orbit shows that the component Sylow fixes only the
central kernel of the original moved cover. Vanishing H¹ of that four-space
then splits the omega-center of the local two-core over the moved factor,
once its component commutators lie in that factor. Characteristic two and
the Sylow fixed-point calculation make every intermediate omega-center
centralize L, including the original point Sylow. Conjugation gives the
corresponding assertion for the entire component orbit on Ω₁Z(T).

The final point-control application discharges both omega centralizations
and the cubic perfect-residual identification. The one remaining assertion
is [Ω₁Z(O₂(L₀T)),L₀] ≤ V; its B.5.1/FF proof remains with the selection owner
qt-d-10-nona5-point-selection. No splitting or movement bound is inferred
from the natural-cover marking alone.
Source: Aschbacher--Smith, 10.2.8--9, pp.749--750, using B.4.8, pp.91--92.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

omit [Finite G] in
/-- The local join preserves the omega-center of its actual two-core. -/
theorem join_normalizes_core_omega :
    localJoin T L ≤ normalizer (omegaCenterIn ((localJoin T L).pCoreIn 2) : Set G) := by
  have hq : localJoin T L ≤ normalizer ((localJoin T L).pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 (localJoin T L)).le_normalizer_map (localJoin T L).subtype
  exact hq.trans (normalizer_le_normalizer_omegaCenterIn _)

/-- The source bound on the entire pair gives the exact first-factor bound by
idempotence of the two-perfect component action. -/
theorem core_omega_component_movement_le_of_orbit_movement_le
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),localOrbit T L⁆ ≤ D.fullModule) :
    ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),L⁆ ≤ ⁅D.fullModule,L⁆ := by
  have hLΩ : L ≤ normalizer (omegaCenterIn ((localJoin T L).pCoreIn 2) : Set G) :=
    ((le_componentOrbit L T).trans le_sup_left).trans join_normalizes_core_omega
  exact (commutator_isPPerfect_idempotent L _ D.faithful.1.2.1
    (IsElementaryAbelian.isPGroup 2 _) hLΩ).symm.le.trans
    (commutator_mono ((commutator_mono le_rfl (le_componentOrbit L T)).trans hcomm) le_rfl)

/-- The positive central cover has no additional fixed points under a component Sylow. -/
theorem moved_sylow_fixed_le_component_fixed
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (P : Sylow 2 L) :
    ⁅D.fullModule,L⁆ ⊓ centralizer ((P : Subgroup L).map L.subtype : Set G) ≤
      centralizer (L : Set G) := by
  intro v hv
  by_contra hn
  let : MulAction L G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp L.subtype)
  have hPS : (P : Subgroup L) ≤ MulAction.stabilizer L v := by
    intro p hp
    change (p : G) * v * (p : G)⁻¹ = v
    rw [hv.2 p (mem_map_of_mem L.subtype hp), mul_inv_cancel_right]
  apply P.not_dvd_index
  apply dvd_trans (show 2 ∣ (MulAction.stabilizer L v).index from ?_)
    (index_dvd_of_le hPS)
  rw [MulAction.index_stabilizer]
  change 2 ∣ (conjugacyOrbit L v).ncard
  rw [moved_orbit_card_of_positive_kernel D hmodel hne hv.1 hn]
  decide

include D in
private theorem component_sylow :
    Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ L) L := by
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hc : (L.subgroupOf (localJoin T L)).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  exact Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    ⟨T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right),
      map_subgroupOf_eq_of_le le_sup_right⟩ hLH hc.subnormal

/-- A component-Sylow-fixed vector of the original moved factor is component-fixed. -/
theorem moved_fixed_by_sylow_intersection
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (↑((T : Subgroup G) ⊓ L) : Set G) ≤
      centralizer (L : Set G) := by
  obtain ⟨P,hP⟩ := component_sylow D
  rw [←hP]
  exact moved_sylow_fixed_le_component_fixed D hmodel hne P

private theorem fullModule_le_core_omega (hfull : D.fullModule = D.moduleSubgroup) :
    D.fullModule ≤ omegaCenterIn ((localJoin T L).pCoreIn 2) := by
  rw [hfull]
  let := D.module_elementary
  intro v hv
  exact (mem_omegaCenterIn_iff _ _).mpr ⟨D.module_le_core hv,
    fun q hq => (D.core_centralizes_module hq v hv).symm,
    elemPow_eq_one_of_isElementaryAbelian v hv⟩

include D in
private theorem join_characteristic_two : localJoin T L ∈ Chapter1.He G := by
  apply Chapter1.lemma_1_1_4_6 T (D.simpleQTKE.evenCharacteristic T)
  refine ⟨?_,fun _ hx => (show (T : Subgroup G) ≤ localJoin T L from le_sup_right) hx⟩
  intro he
  exact D.module_ne_bot (bot_unique (D.module_le_core.trans_eq he))

include D in
/-- The actual core contains the center of every intermediate two-subgroup. -/
theorem interval_omega_eq_core_omega_inf
    (R : Subgroup G) (hQR : (localJoin T L).pCoreIn 2 ≤ R)
    (hRT : R ≤ (T : Subgroup G)) :
    omegaCenterIn R = omegaCenterIn ((localJoin T L).pCoreIn 2) ⊓
      centralizer (R : Set G) := by
  apply omegaCenterIn_eq_inf_of_center_le _ R hQR
  intro r hr
  exact join_characteristic_two D ⟨(show (T : Subgroup G) ≤ localJoin T L from
    le_sup_right) (hRT hr.1), centralizer_le hQR hr.2⟩

/-- H¹ of the positive natural cover splits the actual core omega module over
its first moved factor, provided the earlier source commutator bound holds. -/
theorem core_omega_eq_moved_sup_component_fixed
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),L⁆ ≤ ⁅D.fullModule,L⁆) :
    omegaCenterIn ((localJoin T L).pCoreIn 2) = ⁅D.fullModule,L⁆ ⊔
      (omegaCenterIn ((localJoin T L).pCoreIn 2) ⊓ centralizer (L : Set G)) := by
  obtain ⟨e,⟨c⟩⟩ := hmodel
  let W := ⁅D.fullModule,L⁆
  let Ω := omegaCenterIn ((localJoin T L).pCoreIn 2)
  let := source_original_full_moved_elementary D
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨σ,hσ⟩ := BinaryConjugationSection.exists_action_of_central_kernel
    L W (normalizer_commutator_ge_right _ _) π hπ (by
      intro l hl
      have hp : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
        (e.injective (hl.trans e.map_one.symm))
      exact centralizer_le hWV (source_component_core_centralizes_fullModule D
        (mem_map_of_mem L.subtype hp)))
  obtain ⟨p,hp,_⟩ := c.exists_cover_of_fully_moved (specialLinearNatural 3) π hπ σ hσ
    inf_le_right (source_full_moved_eq_commutator D)
  let : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hd : Module.finrank (ZMod 2) (Additive W) = 4 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod] at hc
    have hW : Nat.card (Additive W) = 16 := moved_card_eq_sixteen D ⟨e,⟨c⟩⟩ hne
    rw [hW] at hc
    exact Nat.pow_right_injective (by decide : 1 < 2) hc.symm
  let := OneCohomology.SLThreeCentralExtension.H1_subsingleton_of_four_dimensional_cover σ p hp hd
  let ec : W ≃* Multiplicative (Additive W) := MulEquiv.refl W
  apply OneCohomology.eq_sup_inf_centralizer_of_H1_zero L W Ω c.section_le
    (hWV.trans (fullModule_le_core_omega D hfull)) π hπ ec σ
    (fun l w => hσ l w) ?_ hcomm
  have hcore : L.pCoreIn 2 ≤ (localJoin T L).pCoreIn 2 :=
    (pCoreIn_mono_of_normalizes (le_componentOrbit L T)
      (source_nonnormal_orbit_le_normalizer D hn)).trans
      (pCoreIn_mono_of_normalizes le_sup_left
        (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)))
  rintro _ ⟨l,hl,rfl⟩ z hz
  have hpL : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp
    (e.injective (hl.trans e.map_one.symm))
  exact ((mem_omegaCenterIn_iff _ _).mp hz |>.2.1 l
    (hcore (mem_map_of_mem L.subtype hpL))).symm

/-- The source splitting forces the omega-center of every intermediate subgroup
containing the original component Sylow to centralize that component. -/
theorem interval_omega_centralizes_component
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),L⁆ ≤ ⁅D.fullModule,L⁆)
    (R : Subgroup G) (hQR : (localJoin T L).pCoreIn 2 ≤ R)
    (hRT : R ≤ (T : Subgroup G)) (hPR : (T : Subgroup G) ⊓ L ≤ R) :
    omegaCenterIn R ≤ centralizer (L : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let Ω := omegaCenterIn ((localJoin T L).pCoreIn 2)
  let C := Ω ⊓ centralizer (L : Set G)
  have hsplit : Ω = W ⊔ C := core_omega_eq_moved_sup_component_fixed D hmodel hne hfull hn hcomm
  have hWΩ : W ≤ Ω := hsplit ▸ le_sup_left
  have hCΩ : C ≤ Ω := inf_le_left
  have hWC : W ≤ normalizer (C : Set G) :=
    ((hWΩ.trans Ω.le_centralizer).trans (centralizer_le hCΩ)).trans
      (Subgroup.centralizer_le_normalizer _)
  rw [interval_omega_eq_core_omega_inf D R hQR hRT]
  intro z hz
  have hzprod : z ∈ (W : Set G) * (C : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right W C hWC,←hsplit]
    exact hz.1
  obtain ⟨w,hw,c,hc,rfl⟩ := hzprod
  have hcP : c ∈ centralizer (↑((T : Subgroup G) ⊓ L) : Set G) := centralizer_le inf_le_right hc.2
  have hwP : w ∈ centralizer (↑((T : Subgroup G) ⊓ L) : Set G) := by
    have hh := (centralizer (↑((T : Subgroup G) ⊓ L) : Set G)).mul_mem
      (centralizer_le hPR hz.2) ((centralizer _).inv_mem hcP)
    simpa only [mul_inv_cancel_right] using hh
  exact (centralizer (L : Set G)).mul_mem
    (moved_fixed_by_sylow_intersection D hmodel hne ⟨hw,hwP⟩) hc.2


/-- The single source commutator bound implies the first omega-center assertion
of 10.2.8 on the original ambient Sylow subgroup. -/
theorem orbit_centralizes_sylow_omega_of_commutator_le
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),L⁆ ≤ ⁅D.fullModule,L⁆) :
    localOrbit T L ≤ centralizer (omegaCenterIn (T : Subgroup G) : Set G) := by
  have hQT : (localJoin T L).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (localJoin T L) (T.subtype le_sup_right)
  have hLZ := le_centralizer_iff.mp
    (interval_omega_centralizes_component D hmodel hne hfull hn hcomm
      (T : Subgroup G) hQT le_rfl inf_le_left)
  exact iSup_conjugates_le_of_le_normalizer L (T : Subgroup G) _ hLZ
    (((T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_omegaCenterIn _)).trans
      (normalizer_le_normalizer_centralizer _))

/-- The same source bound fixes the omega-center of the original point Sylow;
no conjugation of the point or Sylow subgroup is needed. -/
theorem component_centralizes_point_omega_of_commutator_le
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),L⁆ ≤ ⁅D.fullModule,L⁆)
    {v : G} (hv : v ∈ D.fullModule) (hvL : v ∈ centralizer (L : Set G)) :
    L ≤ centralizer (omegaCenterIn ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G) := by
  have hQT : (localJoin T L).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (localJoin T L) (T.subtype le_sup_right)
  have hQC : (localJoin T L).pCoreIn 2 ≤ centralizer ({v} : Set G) := by
    intro q hq
    exact mem_centralizer_singleton_iff.mpr
      (D.core_centralizes_module hq v (hfull ▸ hv)).symm
  apply le_centralizer_iff.mp
  exact interval_omega_centralizes_component D hmodel hne hfull hn hcomm
    _ (le_inf hQT hQC) inf_le_left
    (le_inf inf_le_left (fun l hl => mem_centralizer_singleton_iff.mpr (hvL l hl.2)))

/-- The actual exceptional point case follows from one source commutator bound,
with both omega-center statements and the characteristic residual discharged. -/
theorem point_case_of_core_omega_commutator_le
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),L⁆ ≤ ⁅D.fullModule,L⁆)
    {v : G} (hv : v ∈ D.fullModule) (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G)) : BinaryThreePointCase D v := by
  obtain ⟨e,he⟩ := hmodel
  have hmodel : BinaryThreeNatural D := ⟨e,he⟩
  exact Or.inr ⟨three_dvd_quotient D hmodel,
    orbit_centralizes_sylow_omega_of_commutator_le D hmodel hne hfull hn hcomm,
    point_omega_residual_of_component_centralizes D e hn hv hvL hv0
      (component_centralizes_point_omega_of_commutator_le D hmodel hne hfull hn hcomm hv hvL)⟩

/-- Literal point-control application, including the initially fixed vectors.
The remaining commutator bound is retained by the selection assembly owner. -/
theorem pointSylowControl_of_core_omega_commutator_le
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),L⁆ ≤ ⁅D.fullModule,L⁆)
    (hhalf : HalfSylowUnique D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    PointSylowControl D t := by
  apply pointSylowControl_of_positive_kernel_centralizes_omega D hmodel hne hhalf ht htn hcross
    (orbit_centralizes_sylow_omega_of_commutator_le D hmodel hne hfull (fun hn => htn (hn ht)) hcomm)
  intro v hv _ _ _ _ _
  exact component_centralizes_point_omega_of_commutator_le D hmodel hne hfull
    (fun hn => htn (hn ht)) hcomm (partner_le_fullModule D ht hv) (hcross hv)

/-- The precise remaining source movement assertion suffices for the positive
binary-three branch of the parent's point-control contract. -/
theorem pointSylowControl_of_core_omega_orbit_movement_le
    (hmodel : BinaryThreeNatural D) (hne : sourceMovedFixed D ≠ ⊥)
    (hfull : D.fullModule = D.moduleSubgroup)
    (hcomm : ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),localOrbit T L⁆ ≤ D.fullModule)
    (hhalf : HalfSylowUnique D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    PointSylowControl D t :=
  pointSylowControl_of_core_omega_commutator_le D hmodel hne hfull
    (core_omega_component_movement_le_of_orbit_movement_le D hcomm) hhalf ht htn hcross

end CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
