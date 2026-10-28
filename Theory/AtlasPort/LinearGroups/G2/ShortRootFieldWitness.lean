module

public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.RootElements
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.FieldAction
public import Theory.GroupAction.AutomorphismFixedSubgroup


/-!
# A short-root involution fixed by the field action

The root element C(1) is fixed by every coefficient field automorphism.
Its displacement image on the split octonions contains the identity.
Highest-long-root displacements have zero fourth coordinate, so their
images cannot contain the identity. Every octonion automorphism fixes the
identity, making this obstruction conjugacy invariant. Since every
Sylow-central involution is long-root, C(1) is not two-central.

Source: Aschbacher–Smith, 16.3.9, printed p.1181, and I.2.2(5b), p.409.
The imported octonion root formulas retain LICENSES/ATLAS.txt attribution.
-/

public section

open Subgroup Theory.GroupTheory
namespace Atlas.G2.ShortRootFieldWitness
open Atlas.SplitOctonion Explicit
variable {F : Type*} [Field F] [CharP F 2]

theorem rootC_one_displacement :
    ∃ v : Carrier F, (rootC (1 : F)).val v = v + unit := by
  refine ⟨![0,0,0,1,0,0,0,1], ?_⟩
  ext i
  fin_cases i <;> simp [rootC, rootCEquiv, rootCLinear, rootCApply, unit,
    CharTwo.neg_eq, CharTwo.add_self_eq_zero]

theorem rootC_one_not_long :
    ¬ EvenInvolutionGeometry.IsLongRootElement (rootC (1 : F)) := by
  rintro ⟨g,a,_,he⟩
  obtain ⟨v,hv⟩ := rootC_one_displacement (F := F)
  have hv' : g.val ((rootA a).val ((g⁻¹).val v)) = v + unit := by
    rw [he] at hv
    exact hv
  have hh := congrArg (g⁻¹).val hv'
  change g.val.symm (g.val ((rootA a).val (g.val.symm v))) =
    (g⁻¹).val (v + unit) at hh
  rw [LinearEquiv.symm_apply_apply, map_add, automorphism_unit] at hh
  have h3 := congrFun hh 3
  have hz : (1 : F) = 0 := by
    simpa [rootA,rootAEquiv,rootALinear,rootAApply,unit] using h3.symm
  exact one_ne_zero hz

theorem rootC_one_not_twoCentral [Finite F] :
    ¬ IsSylowCentralInvolution (rootC (1 : F)) := by
  rintro ⟨ho,S,hm,hc⟩
  apply rootC_one_not_long (F := F)
  apply EvenInvolutionGeometry.central_involution_isLongRoot S hm
    (ho ▸ pow_orderOf_eq_one _) ?_ ?_
  · intro y hy
    exact (mem_centralizer_singleton_iff.mp (hc hy)).symm
  · intro he
    simp [he] at ho

omit [CharP F 2] in
theorem fieldEquiv_rootC (σ : F ≃+* F) (a : F) :
    fieldEquiv σ (rootC a) = rootC (σ a) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [fieldEquiv,transportAutomorphism,transportLinear,
    mapCoefficients,rootC,rootCEquiv,rootCLinear,rootCApply]

omit [CharP F 2] in
theorem rootC_one_fixed (σ : F ≃+* F) :
    rootC (1 : F) ∈ (LieAutomorphismExtensions.fieldAction σ).fixedSubgroup := by
  rw [MulAut.mem_fixedSubgroup]
  change fieldEquiv σ (rootC 1) = rootC 1
  rw [fieldEquiv_rootC, map_one]

end Atlas.G2.ShortRootFieldWitness
