module
public import Theory.Representation.BinaryEndpointInduction.ParabolicSeedMarking
public import Theory.Representation.BinaryEndpointInduction.SurvivorModels
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The singular fixed space of the actual endpoint radical

The three literal endpoint shears are commutators of elements in the
endpoint two-core with elements of the same endpoint parabolic. Their
common fixed space in the actual right-row exterior model is singular.
Thus the statement retains the original radical actors, not merely a
natural-three constituent label.
-/
public noncomputable section
open Matrix Subgroup
open scoped MatrixGroups commutatorElement
namespace BinaryEndpointInduction

/-- The three original radical directions below the fixed first row. -/
@[expose] def endpointShear (i : Fin 3) : SL(4,ZMod 2) :=
  SpecialLinearGroup.transvection (Fin.succ_ne_zero i) (1 : ZMod 2)

private theorem shear_endpoint : ∀ i : Fin 3, endpointShear i ∈ endpointParabolic := by
  change ∀ (i : Fin 3) (k : Fin 4), (endpointShear i).val 0 k=if k=0 then 1 else 0
  decide +kernel

private theorem shear_kernel : ∀ i : Fin 3,
    (⟨endpointShear i,shear_endpoint i⟩ : endpointParabolic) ∈ endpointLevi.ker := by
  decide +kernel

private def partner : Fin 3 → Fin 3 := ![1,2,0]
private def lowerShear (i : Fin 3) : SL(4,ZMod 2) :=
  SpecialLinearGroup.transvection
    (show i.succ ≠ (partner i).succ by fin_cases i <;> decide) (1 : ZMod 2)

private theorem lower_endpoint : ∀ i : Fin 3, lowerShear i ∈ endpointParabolic := by
  change ∀ (i : Fin 3) (k : Fin 4), (lowerShear i).val 0 k=if k=0 then 1 else 0
  decide +kernel

private theorem shear_commutator : ∀ i : Fin 3,
    ⁅endpointShear (partner i),lowerShear i⁆=endpointShear i := by
  decide +kernel

/-- Each actual shear belongs to the component commutator of the endpoint
two-core; the source core image can therefore lift it literally. -/
theorem endpointShear_mem_commutator (i : Fin 3) :
    endpointShear i ∈ ⁅endpointParabolic.pCoreIn 2,endpointParabolic⁆ := by
  rw [←shear_commutator i]
  apply commutator_mem_commutator _ (lower_endpoint i)
  exact mem_map_of_mem endpointParabolic.subtype
    ((show endpointLevi.ker ≤ pCore 2 endpointParabolic from
      le_sSup ⟨inferInstance,endpointLevi_kernel_two⟩) (shear_kernel (partner i)))

private theorem singular_check : ∀ x : Fin 6 → ZMod 2,
    (∀ i : Fin 3, x ᵥ* survivorModelMatrix false ((endpointShear i)⁻¹)=x) →
      Atlas.Order20160A8.Bivectors.pfaffian x=0 := by
  decide +kernel

/-- A vector fixed by the actual endpoint radical shears is singular in
the genuine exterior-six model. -/
theorem exterior_singular_of_endpoint_fixed (x : Fin 6 → ZMod 2)
    (hx : ∀ i : Fin 3, x ᵥ* survivorModelMatrix false ((endpointShear i)⁻¹)=x) :
    Atlas.Order20160A8.Bivectors.pfaffian x=0 := singular_check x hx

end BinaryEndpointInduction
