module
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.AffineCentralizer
public import Theory.SpecificGroups.SL2.Affine.Action

/-!
# Fusion of nonzero translations

The determinant-one natural action is transitive on nonzero vectors. The
literal affine coordinates therefore conjugate any two nonidentity elements
of the translation core by an element of the original affine subgroup.
Source: the natural-module fusion used in Aschbacher–Smith §5.3.6–7,
printed p.660 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearAmbientGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {G : Type*} [Group G]

/-- The actual affine group conjugates any two nonzero elements of its core. -/
theorem affine_core_transitive
    (X : Subgroup G) (e : X ≃* SL2.Affine F)
    (z w : G) (hz : z ∈ X.pCoreIn 2) (hw : w ∈ X.pCoreIn 2)
    (hz1 : z ≠ 1) (hw1 : w ≠ 1) :
    ∃ g ∈ X, g * z * g⁻¹ = w := by
  let z' : X := ⟨z,pCoreIn_le 2 X hz⟩
  let w' : X := ⟨w,pCoreIn_le 2 X hw⟩
  have hz' : z' ∈ pCore 2 X := (mem_map_iff_mem X.subtype_injective).mp hz
  have hw' : w' ∈ pCore 2 X := (mem_map_iff_mem X.subtype_injective).mp hw
  have ht (x : X) (hx : x ∈ pCore 2 X) : e x ∈ SL2.translations F := by
    rw [← SL2.affine_twoCore_eq,← pCore_map_iso 2 e]
    exact mem_map_of_mem e.toMonoidHom hx
  obtain ⟨v,hv⟩ := (SL2.range_inl_eq_translations F).symm ▸ ht z' hz'
  obtain ⟨u,hu⟩ := (SL2.range_inl_eq_translations F).symm ▸ ht w' hw'
  have hv0 : v.toAdd ≠ 0 := by
    intro h
    have he : e z' = 1 := hv.symm.trans (by rw [show v = 1 from Multiplicative.toAdd.injective h,map_one])
    exact hz1 (congrArg X.subtype (e.injective (he.trans (map_one e).symm)))
  have hu0 : u.toAdd ≠ 0 := by
    intro h
    have he : e w' = 1 := hu.symm.trans (by rw [show u = 1 from Multiplicative.toAdd.injective h,map_one])
    exact hw1 (congrArg X.subtype (e.injective (he.trans (map_one e).symm)))
  obtain ⟨a,ha⟩ := SL2.exists_mulVec_eq F v.toAdd u.toAdd hv0 hu0
  let g : X := e.symm (SemidirectProduct.inr a)
  refine ⟨g,g.property,?_⟩
  have hg : g * z' * g⁻¹ = w' := by
    apply e.injective
    simp only [map_mul,map_inv,g,e.apply_symm_apply,← hv,← hu,SL2.conjugate_inl]
    apply congrArg SemidirectProduct.inl
    exact Multiplicative.toAdd.injective ha
  exact congrArg X.subtype hg

end Matrix.PSL3.LinearAmbientGeometry
