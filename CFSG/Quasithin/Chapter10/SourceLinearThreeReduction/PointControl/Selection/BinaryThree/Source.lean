module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.ZeroKernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.CoreOmega
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.PairActor
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.Movement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Definitions

/-!
# Binary-three point geometry and the selection consumer

The fixed-layer clause, zero-kernel point-Sylow calculation and all
positive-kernel point geometry are proved on the original moved cover.
The sharp offender bound on the full module gives the fixed supplement
for every maximum elementary subgroup. Thompson commutator generation
then proves [Ω₁Z(O₂(L₀T)),L₀] ≤ V. Both omega-center centralizations and
the characteristic perfect-residual identification follow without an
additional movement premise.

The binary-three assembly retains only source 10.2.5's half-Sylow
normalizer bound in the zero-kernel row, owned by
qt-d-10-nona5-half-sylow-unique. Module choice and rank-one stabilization
remain with qt-d-10-nona5-point-selection. The conditional selection
assemblies below do not assert unconditional SelectionAt.
Source: Aschbacher--Smith, 10.2.8--9, printed pp.749--750.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Every escaping point distinguishes the components, even when its initial
membership in the L₀-fixed layer has not been excluded. -/
theorem escaping_point_stabilizes
    (hmodel : BinaryThreeNatural D) (hhalf : HalfSylowUnique D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hvne : v ≠ 1) (hout : ¬ centralizer ({v} : Set G) ≤ D.maximalLocal) :
    v ∉ centralizer (localOrbit T L : Set G) ∧
      (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤ normalizer (L : Set G) :=
  Selection.escaping_point_stabilizes D hhalf
    (fixed_layer_centralizes_half_sylow D hmodel ht htn hcross) ht htn hcross hv hvne hout

/-- The fixed-layer input of the original binary-three point consumer is discharged. -/
theorem pointSylowControl_of_point_cases
    (hmodel : BinaryThreeNatural D) (hhalf : HalfSylowUnique D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hpoints : ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom,
      v ≠ 1 → v ∉ centralizer (localOrbit T L : Set G) →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
        (D.maximalLocal ⊓ centralizer ({v} : Set G)) → BinaryThreePointCase D v) :
    PointSylowControl D t :=
  pointSylowControl_of_binaryThree_geometry D hhalf ht htn hcross
    ⟨fixed_layer_centralizes_half_sylow D hmodel ht htn hcross,hpoints⟩

omit D in
/-- The exact remaining binary-three point calculation. Its fixed-layer
clause is no longer an additional source premise. -/
@[expose] def PointCasesAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule → D.fullModule = D.moduleSubgroup →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) → BinaryThreeNatural D →
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) →
    ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) →
      HalfSylowUnique D →
      ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom,
        v ≠ 1 → v ∉ centralizer (localOrbit T L : Set G) →
        Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
          (D.maximalLocal ⊓ centralizer ({v} : Set G)) → BinaryThreePointCase D v

omit D in
/-- The conditional point calculation supplies the original geometry interface. -/
theorem geometryAt_of_point_cases (hpoints : PointCasesAt T) : BinaryThreeGeometryAt T := by
  intro hmany L D hmin hfull hna hmodel hJ t ht htn hcross hhalf
  exact ⟨fixed_layer_centralizes_half_sylow D hmodel ht htn hcross,
    hpoints hmany L D hmin hfull hna hmodel hJ t ht htn hcross hhalf⟩

omit D in
/-- The literal selection consumer now requires only binary-three point
calculations, alongside the still separate module-choice and rank-one geometry. -/
theorem selectionAt_of_point_cases
    (hchoice : ModuleChoiceAt T) (hrankOne : RankOneGeometryAt T)
    (hpoints : PointCasesAt T) : SelectionAt T :=
  selectionAt_of_source_geometry hchoice hrankOne (geometryAt_of_point_cases hpoints)

omit D in
/-- Application to the parent's original point-centralizer assembly. The
selection owner retains module choice, rank-one geometry and the remaining
binary-three point cases; the parent retains its other source steps. -/
theorem source_nonnormalPointControl_of_point_cases
    (hchoice : ModuleChoiceAt T) (hrankOne : RankOneGeometryAt T)
    (hpoints : PointCasesAt T) (hhalf : HalfSylowUniqueAt T)
    (hquasi : QuasisimpleExclusionAt T) (hconstrained : ConstrainedExclusionAt T) :
    SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf
    (selectionAt_of_point_cases hchoice hrankOne hpoints) hquasi hconstrained

omit D in
/-- Only the positive fixed-kernel calculation from source 10.2.8 remains.
All original quotient, point, saturation and half-uniqueness inputs are retained. -/
@[expose] def PositiveKernelPointCasesAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule → D.fullModule = D.moduleSubgroup →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) → BinaryThreeNatural D →
    sourceMovedFixed D ≠ ⊥ →
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) →
    ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) →
      HalfSylowUnique D →
      ∀ v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom,
        v ≠ 1 → v ∉ centralizer (localOrbit T L : Set G) →
        Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
          (D.maximalLocal ⊓ centralizer ({v} : Set G)) → BinaryThreePointCase D v

omit D in
/-- Discharge the zero-kernel row without an additional point-geometry callback. -/
theorem pointCasesAt_of_positive_kernel
    (hN : HalfUniqueness.StabilizerNormalizerAt T)
    (hpositive : PositiveKernelPointCasesAt T) : PointCasesAt T := by
  intro hmany L D hmin hfull hna hmodel hJ t ht htn hcross hhalf v hv hvne hv0 hs
  by_cases hzero : sourceMovedFixed D = ⊥
  · exact point_case_of_zero_kernel D hmodel hzero
      (hN hmany L D (fun hn => htn (hn ht)) hna) ht htn hcross hv hvne hs
  · exact hpositive hmany L D hmin hfull hna hmodel hzero hJ t ht htn hcross
      hhalf v hv hvne hv0 hs

omit D in
/-- The literal selection consumer with only the positive binary-three row left. -/
theorem selectionAt_of_positive_kernel
    (hchoice : ModuleChoiceAt T) (hrankOne : RankOneGeometryAt T)
    (hN : HalfUniqueness.StabilizerNormalizerAt T)
    (hpositive : PositiveKernelPointCasesAt T) : SelectionAt T :=
  selectionAt_of_point_cases hchoice hrankOne (pointCasesAt_of_positive_kernel hN hpositive)

omit D in
/-- Actual application to the parent source consumer. Module choice, rank-one
stabilization and positive-kernel geometry remain with the selection owner. -/
theorem source_nonnormalPointControl_of_positive_kernel
    (hchoice : ModuleChoiceAt T) (hrankOne : RankOneGeometryAt T)
    (hN : HalfUniqueness.StabilizerNormalizerAt T)
    (hpositive : PositiveKernelPointCasesAt T) (hhalf : HalfSylowUniqueAt T)
    (hquasi : QuasisimpleExclusionAt T) (hconstrained : ConstrainedExclusionAt T) :
    SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf
    (selectionAt_of_positive_kernel hchoice hrankOne hN hpositive) hquasi hconstrained

omit D in
/-- The remaining movement assertion from the FF argument in 10.2.8, on the
actual selected module and local two-core. Its producer remains in this task. -/
@[expose] def CoreOmegaMovementAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule → D.fullModule = D.moduleSubgroup →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) → BinaryThreeNatural D →
    sourceMovedFixed D ≠ ⊥ →
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) →
    ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) →
      HalfSylowUnique D →
      ⁅omegaCenterIn ((localJoin T L).pCoreIn 2),localOrbit T L⁆ ≤ D.fullModule

omit D in
/-- Discharge every positive-kernel point case from the single earlier movement
bound; saturation and the original point remain those of the consumer. -/
theorem positiveKernelPointCasesAt_of_core_omega_movement
    (hmove : CoreOmegaMovementAt T) : PositiveKernelPointCasesAt T := by
  intro hmany L D hmin hfull hna hmodel hne hJ t ht htn hcross hhalf v hv _ hv0 _
  exact point_case_of_core_omega_commutator_le D hmodel hne hfull
    (fun hn => htn (hn ht))
    (core_omega_component_movement_le_of_orbit_movement_le D
      (hmove hmany L D hmin hfull hna hmodel hne hJ t ht htn hcross hhalf))
    (partner_le_fullModule D ht hv) (hcross hv) hv0

omit D in
/-- The literal selection assembly after the omega-center and residual steps.
Module choice, rank-one geometry and the remaining movement bound stay with
qt-d-10-nona5-point-selection; the normalizer bound has its existing owner. -/
theorem selectionAt_of_core_omega_movement
    (hchoice : ModuleChoiceAt T) (hrankOne : RankOneGeometryAt T)
    (hN : HalfUniqueness.StabilizerNormalizerAt T)
    (hmove : CoreOmegaMovementAt T) : SelectionAt T :=
  selectionAt_of_positive_kernel hchoice hrankOne hN
    (positiveKernelPointCasesAt_of_core_omega_movement hmove)

omit D in
/-- Actual application to the parent's original source point-control theorem. -/
theorem source_nonnormalPointControl_of_core_omega_movement
    (hchoice : ModuleChoiceAt T) (hrankOne : RankOneGeometryAt T)
    (hN : HalfUniqueness.StabilizerNormalizerAt T)
    (hmove : CoreOmegaMovementAt T) (hhalf : HalfSylowUniqueAt T)
    (hquasi : QuasisimpleExclusionAt T) (hconstrained : ConstrainedExclusionAt T) :
    SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf
    (selectionAt_of_core_omega_movement hchoice hrankOne hN hmove) hquasi hconstrained

omit D in
/-- The FF argument now proves the exact source movement contract. -/
theorem coreOmegaMovementAt : CoreOmegaMovementAt T := by
  intro _ L D _ hfull _ hmodel hne hJ t ht htn hcross _
  exact core_omega_orbit_movement_le D hmodel hne hfull hJ ht htn hcross

omit D in
/-- Every positive-kernel point case is discharged on its original quotient. -/
theorem positiveKernelPointCasesAt : PositiveKernelPointCasesAt T :=
  positiveKernelPointCasesAt_of_core_omega_movement coreOmegaMovementAt

omit D in
/-- The binary-three geometry only retains the earlier zero-kernel normalizer
bound 10.2.5, owned by qt-d-10-nona5-half-sylow-unique. -/
theorem binaryThreeGeometryAt_of_stabilizer_normalizer
    (hN : HalfUniqueness.StabilizerNormalizerAt T) : BinaryThreeGeometryAt T :=
  geometryAt_of_point_cases (pointCasesAt_of_positive_kernel hN positiveKernelPointCasesAt)

omit D in
/-- Selection after completing all positive-kernel binary-three geometry.
The selection owner still owes module choice and rank-one geometry. -/
theorem selectionAt_of_module_choice_rank_one_and_stabilizer
    (hchoice : ModuleChoiceAt T) (hrankOne : RankOneGeometryAt T)
    (hN : HalfUniqueness.StabilizerNormalizerAt T) : SelectionAt T :=
  selectionAt_of_source_geometry hchoice hrankOne
    (binaryThreeGeometryAt_of_stabilizer_normalizer hN)

omit D in
/-- Actual parent application with the positive-kernel premise discharged.
Module choice and rank-one geometry stay with the selection owner; the
remaining earlier source premises stay with their existing assembly owners. -/
theorem source_nonnormalPointControl_of_module_choice_rank_one_and_stabilizer
    (hchoice : ModuleChoiceAt T) (hrankOne : RankOneGeometryAt T)
    (hN : HalfUniqueness.StabilizerNormalizerAt T) (hhalf : HalfSylowUniqueAt T)
    (hquasi : QuasisimpleExclusionAt T) (hconstrained : ConstrainedExclusionAt T) :
    SourceNonnormalPointControlAt T :=
  source_nonnormalPointControl_of_sourceSteps hhalf
    (selectionAt_of_module_choice_rank_one_and_stabilizer hchoice hrankOne hN)
    hquasi hconstrained

end CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
