module

public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# A strict heptad overgroup of the common four-group normalizer

The common four-group fixes exactly the literal Witt heptad numbered 205 in the
native design. Any element normalizing the four-group preserves its entire fixed
set, so its full ambient normalizer lies in the heptad stabilizer. The word
A⁻¹ B⁻² A in the certified M22 generators preserves this heptad but moves the
four-group, proving strictness. The existing self-centralizing heptad two-core
then gives the required equality of the generalized Fitting subgroup and O₂.

Source: Aschbacher--Smith, the sporadic paragraph of 15.3.43, printed p.1140;
1.1.5(3)(f), printed p.502; GLS3 Table 5.3d. All stabilizers and normalizers here
are subgroups of native M23, and the Fitting condition is intrinsic to the
heptad stabilizer.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.FourNormalizers
open FusionCertificate ElementarySylow
set_option maxRecDepth 100000
set_option Elab.async false

private noncomputable def element (i : Fin 128) : M23 :=
  ⟨perm i, rawSubgroup_le (perm_mem i)⟩

/-- The literal fixed heptad of the common four-group. -/
def fixedSet : Finset (Fin 23) := {0, 5, 6, 11, 12, 17, 18}

theorem fixedSet_mem : fixedSet ∈ m23Blocks := by
  have he : fixedSet = m23BlockAt 205 := by decide +kernel
  rw [he, m23Blocks]
  exact Finset.mem_image.mpr ⟨205, Finset.mem_univ _, rfl⟩

private theorem common_fixes : ∀ (i : Fin 4) (a : Fin 23), a ∈ fixedSet →
    pointTable (commonIndex i) a = a := by decide +kernel

private theorem first_fixed : ∀ a : Fin 23,
    pointTable (commonIndex 1) a = a ↔ a ∈ fixedSet := by decide +kernel

theorem mem_fixedSet_iff (a : Fin 23) :
    a ∈ fixedSet ↔ ∀ u ∈ common, u • a = a := by
  constructor
  · intro ha u hu
    obtain ⟨i, hi⟩ := (mem_common u).mp hu
    change u.val a = a
    rw [← hi]
    exact common_fixes i a ha
  · intro ha
    exact (first_fixed a).mp (ha (element (commonIndex 1))
      ((mem_common _).mpr ⟨1, rfl⟩))

/-- Normalization of the four-group preserves all its common fixed points. -/
theorem normalizer_le_stabilizer : normalizer (common : Set M23) ≤
    MulAction.stabilizer M23 fixedSet := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro a ha
  apply (mem_fixedSet_iff _).mpr
  intro u hu
  have hv := (mem_normalizer_iff.mp ((normalizer (common : Set M23)).inv_mem hg) u).mp hu
  have hf := (mem_fixedSet_iff a).mp ha _ hv
  have he := congrArg (fun b : Fin 23 => g • b) hf
  simpa only [inv_inv, mul_smul, smul_inv_smul] using he

private def movingPerm : Equiv.Perm (Fin 23) :=
  m23M22GeneratorA⁻¹ * m23M22GeneratorB⁻¹ * m23M22GeneratorB⁻¹ * m23M22GeneratorA

private noncomputable def movingElement : M23 :=
  (⟨m23M22GeneratorA, m23M22GeneratorA_mem_M23⟩ : M23)⁻¹ *
    (⟨m23M22GeneratorB, m23M22GeneratorB_mem_M23⟩ : M23)⁻¹ *
    (⟨m23M22GeneratorB, m23M22GeneratorB_mem_M23⟩ : M23)⁻¹ *
    ⟨m23M22GeneratorA, m23M22GeneratorA_mem_M23⟩

private theorem moving_preserves : ∀ a : Fin 23,
    a ∈ fixedSet → movingPerm a ∈ fixedSet := by decide +kernel

private theorem moving_changes : ∀ i : Fin 4,
    movingPerm * perm (commonIndex 1) * movingPerm⁻¹ ≠ perm (commonIndex i) := by
  decide +kernel

/-- A short word in certified native generators proves proper containment. -/
theorem normalizer_lt_stabilizer : normalizer (common : Set M23) <
    MulAction.stabilizer M23 fixedSet := by
  apply lt_of_le_not_ge normalizer_le_stabilizer
  intro h
  have hm : movingElement ∈ MulAction.stabilizer M23 fixedSet :=
    MulAction.mem_stabilizer_finset'.mpr moving_preserves
  have hc := (mem_normalizer_iff.mp (h hm) (element (commonIndex 1))).mp
    ((mem_common _).mpr ⟨1, rfl⟩)
  obtain ⟨i, hi⟩ := (mem_common _).mp hc
  exact moving_changes i hi.symm

/-- The overgroup has the intrinsic generalized-Fitting condition required by
maximality in the sporadic source argument. -/
theorem stabilizer_characteristicTwo :
    generalizedFitting (MulAction.stabilizer M23 fixedSet) =
      pCore 2 (MulAction.stabilizer M23 fixedSet) := by
  apply Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing
  exact (heptad_stabilizer_local_structure fixedSet_mem (MulEquiv.refl _)).2.1

end Sporadic.Mathieu.M23Geometry.FourNormalizers
