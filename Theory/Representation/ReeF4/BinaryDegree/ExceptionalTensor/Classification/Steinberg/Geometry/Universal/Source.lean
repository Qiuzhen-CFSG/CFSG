module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4Semisimple
public import Theory.AlgebraicGroup.Semisimple.IsogenySource
public import Theory.AlgebraicGroup.Borel.AdjointCenter
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected.Realization
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.KernelContainment
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.RootCurvePowers
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Normalization
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.CoordinatePowers

/-!
# Universality of the literal characteristic-two F4 carrier

Actual root generation makes the four standard coroot coordinates an
isomorphism of tori. The constructed opposite-root SL2 charts are Cartan
normalized; their genuine regular root-curve lifts provide characteristic-power
lifts of those coroots through any connected incoming isogeny. The kernel is
central. The independent universal semisimple-center theorem puts it in the
connected maximal-torus lift, where the coroot calculation proves it trivial.
Coordinate-power descent then constructs a reverse isogeny, including the
inseparable case without claiming a regular inverse of the incoming map.

Only GLS3 1.9.5(h), center containment in every maximal torus of a semisimple
group, remains explicit with its shared source producer. All literal F4
root-model, chart, lifting and coordinate-descent inputs are discharged.
Source: GLS3 1.10.4(b), 1.10.5 and the fundamental-coroot criterion 1.12.5(b).
-/

public section

open Theory.AlgebraicGroup
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

/-- The only remaining source premise is the universal semisimple-center theorem. -/
theorem carrier_isUniversalVersion_of_semisimple_centers
    (hcenter : ∀ (H : Variety F) [AlgebraicGroup H], IsSemisimpleAlgebraicGroup H →
      ∀ T : ClosedSubgroup H, IsMaximalTorus T →
        Subgroup.center (Variety.Point H) ≤ T.toSubgroup) :
    IsUniversalVersion (F4Chevalley.Carrier (k := F)) := by
  classical
  have hsemi := F4Chevalley.carrier_isSemisimple (k := F)
  refine ⟨hsemi, ?_⟩
  intro H _ hH φ hφ
  let M := RootModel.Corrected.rootSystemModel (F := F)
  let : AlgebraicGroup M.torus.carrierVariety := M.torus.carrierAlgebraicGroup
  have hgen := M.f4_rootGeneration_of_torus_conjugacy_and_unique_weights
    (F4Chevalley.TorusConjugacy.model_torus_conjugate M) F4Chevalley.concreteRootSubgroup_eq
  have hsep := M.f4CorootCoordinates_injective_of_rootGeneration hsemi hgen
  obtain ⟨e,he⟩ := M.f4CorootProduct_iso_of_coordinates_injective hsep
  let rootGroups (r : M.rootData.Root) : AlgebraicGroup (M.rootData.rootSubgroup r).carrierVariety :=
    (M.rootData.rootSubgroup r).carrierAlgebraicGroup
  let C (i : Fin 4) := Classical.choice (M.f4SimpleRoot_nonempty_sl2Chart i)
  let x (i : Fin 4) :=
    ((M.rootData.rootSubgroup (M.f4SimpleRoot i)).inclusion.comp (C i).plus.hom).toVariety
  let y (i : Fin 4) :=
    ((M.rootData.rootSubgroup (M.rootData.neg (M.f4SimpleRoot i))).inclusion.comp
      (C i).minus.hom).toVariety
  have hword (i : Fin 4) (t) : (binaryCorootWord (x i) (y i)).toFun t =
      M.torus.inclusion.onPoints ((M.rootData.rootCocharacter (M.f4SimpleRoot i)).onPoints t) :=
    M.f4_binaryCorootWord_eq_of_chart e he _ (C i)
      (M.f4_binaryOppositeRootSL2Chart_isCartan i (C i)) t
  obtain ⟨a,μ,hμ⟩ := M.f4_coroot_power_lifts_of_root_curve_lifts φ hφ x y hword
    (fun i => M.exists_root_curve_binary_power_lift φ hφ hH _ (C i).plus)
    (fun i => M.exists_root_curve_binary_power_lift φ hφ hH _ (C i).minus)
  have hkernel : φ.kernel ≤ (isogenyTorusLift φ M.torus).toSubgroup :=
    le_trans (isogeny_kernel_le_center_of_connected φ hφ hH)
      (hcenter H (isogeny_source_semisimple φ hφ hH hsemi) _
        (isogenyTorusLift_isMaximalTorus φ hφ M.torus M.maximalTorus))
  have hinj := f4_incoming_isogeny_injective_of_torus_coroot_lifts M φ hφ e he hkernel μ a hμ
  obtain ⟨ψ,hψ,_⟩ := f4_reverse_isogeny_of_coordinate_powers φ hφ.1
    (f4_coordinate_powers_of_injective_isogeny φ hH hφ hinj)
  exact ⟨ψ,hψ⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry
