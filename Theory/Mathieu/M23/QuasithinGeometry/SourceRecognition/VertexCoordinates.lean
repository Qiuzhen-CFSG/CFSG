module
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions

/-!
# Edge coordinates for either linear-three parabolic orientation

Inverse transpose commutes with Frobenius, so it extends to the actual
PSL₃(4) ⋊ C₂. It sends the standard line parabolic to a point stabilizer;
point transitivity then moves either orientation to the point corresponding
to the native adjacent pair. The resulting map into the M23 pair stabilizer
preserves the whole linear subgroup by an explicit equation on every element.

This supplies the initial edge marking in source 5.2.20(5). It does not assert
agreement with an independently chosen heptad marking on the local intersection.
Source: Aschbacher--Smith, printed pp.655--657, 5.2.16, 5.2.18 and 5.2.20(5).
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace Sporadic.Mathieu.M23Geometry.SourceVertex
open Matrix Matrix.PSL3Four Matrix.PSL3.OuterSolvable
open Projectivization

private def axis (i : Fin 3) : PG := mk F (Pi.single i 1) (by simp)

private theorem fixes_axis (A : SL) (i : Fin 3) :
    A • axis i = axis i ↔ ∀ j, j ≠ i → A j i = 0 := by
  rw [axis,smul_mk,mk_eq_mk_iff]
  constructor
  · rintro ⟨r,hr⟩ j hj
    have hh := congrFun hr j
    change (r : F) * (Pi.single i 1 : Fin 3 → F) j = (A.val *ᵥ Pi.single i 1) j at hh
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hj] using hh.symm
  · intro h
    have hn : A i i ≠ 0 := by
      intro hz
      have hv : A • (Pi.single i 1 : Fin 3 → F) = 0 := by
        change A.val *ᵥ Pi.single i 1 = 0
        ext j
        by_cases hj : j = i
        · subst j
          simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hz
        · simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h j hj
      have hh := (smul_eq_zero_iff_eq A).mp hv
      simp at hh
    refine ⟨Units.mk0 (A i i) hn,?_⟩
    change (A i i) • (Pi.single i 1 : Fin 3 → F) = A.val *ᵥ Pi.single i 1
    ext j
    by_cases hj : j = i
    · subst j
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Pi.single_apply, hj, h j hj]

private theorem point_eq_stabilizer :
    Matrix.PSL3.LinearThree.pointParabolic F = MulAction.stabilizer PSL (axis 0) := by
  apply Subgroup.comap_injective (Matrix.PSL3.projection_surjective F)
  rw [Matrix.PSL3.LinearThree.pointParabolic_comap]
  ext A
  change A ∈ Matrix.PSL3.LinearThree.pointParabolicSL F ↔ A • axis 0 = axis 0
  rw [Matrix.PSL3.LinearThree.mem_pointParabolicSL_iff,fixes_axis]
  constructor
  · rintro ⟨h1,h2⟩ j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact h1
    · exact h2
  · intro h
    exact ⟨h 1 (by decide),h 2 (by decide)⟩

private theorem graph_line_eq_stabilizer :
    (Matrix.PSL3.LinearThree.lineParabolic F).map (graph F).toMonoidHom =
      MulAction.stabilizer PSL (axis 2) := by
  ext x
  obtain ⟨a,rfl⟩ := (graph F).surjective x
  rw [Subgroup.mem_map_equiv, (graph F).symm_apply_apply]
  obtain ⟨A,rfl⟩ := Matrix.PSL3.projection_surjective F a
  change Matrix.PSL3.projection F A ∈ Matrix.PSL3.LinearThree.lineParabolic F ↔
    (graph F) (A : PSL) • axis 2 = axis 2
  have hm : Matrix.PSL3.projection F A ∈ Matrix.PSL3.LinearThree.lineParabolic F ↔
      A ∈ Matrix.PSL3.LinearThree.lineParabolicSL F := by
    change A ∈ (Matrix.PSL3.LinearThree.lineParabolic F).comap _ ↔ _
    rw [Matrix.PSL3.LinearThree.lineParabolic_comap]
  rw [hm]
  rw [graph_mk]
  change _ ↔ (A.transpose)⁻¹ • axis 2 = axis 2
  rw [inv_smul_eq_iff,eq_comm,fixes_axis,
    Matrix.PSL3.LinearThree.mem_lineParabolicSL_iff]
  change (A 2 0 = 0 ∧ A 2 1 = 0) ↔ ∀ j, j ≠ 2 → A 2 j = 0
  constructor
  · rintro ⟨h0,h1⟩ j hj
    fin_cases j
    · exact h0
    · exact h1
    · exact (hj rfl).elim
  · intro h
    exact ⟨h 0 (by decide),h 1 (by decide)⟩

private theorem graph_commute_frobenius : Commute (graph F) pslFrobenius := by
  apply MulEquiv.ext
  intro y
  induction y using QuotientGroup.induction_on with
  | H A =>
    simp only [MulAut.mul_apply,pslFrobenius_mk,graph_mk]
    rw [map_inv]
    congr 2

private def graphExtension : MulAut FieldExtension :=
  SemidirectProduct.congr (graph F) (MulEquiv.refl C2) (by
    intro t
    apply MulEquiv.ext
    intro g
    exact DFunLike.congr_fun (graph_commute_frobenius.pow_right t.toAdd.val).eq g)

private theorem graphExtension_linear (g : PSL) :
    graphExtension (linearInclusion g) = linearInclusion (graph F g) := by
  rfl

private theorem conjugation_linear (g a : PSL) :
    MulAut.conj (linearInclusion g) (linearInclusion a) =
      linearInclusion (MulAut.conj g a) := by
  simp only [MulAut.conj_apply,map_mul,map_inv]

/-- Either standard parabolic admits coordinates in the actual pair stabilizer
with the required edge image and a compatible map on the entire linear subgroup. -/
theorem exists_edge_coordinates (b : Bool) :
    ∃ (e : FieldExtension ≃* pairStabilizer) (δ : MulAut PSL),
      ((Matrix.PSL3.RootPlaneGeometry.parabolic F b).map linearInclusion).map
        e.toMonoidHom =
        (pairStabilizer ⊓ MulAction.stabilizer Sporadic.Mathieu.M23 y.val).subgroupOf pairStabilizer ∧
      ∀ g : PSL, e (linearInclusion g) = (PairPlane.pointwiseEquiv.symm (δ g)).val := by
  have hpoint : ∀ p : PG, ∃ (a : MulAut FieldExtension) (δ : MulAut PSL),
      ((MulAction.stabilizer PSL p).map linearInclusion).map a.toMonoidHom =
        PairPlane.pointParabolic.map linearInclusion ∧
      ∀ g : PSL, a (linearInclusion g) = linearInclusion (δ g) := by
    intro p
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL p PairPlane.planePoint
    refine ⟨MulAut.conj (linearInclusion g),MulAut.conj g,?_,conjugation_linear g⟩
    have hf : (MulAut.conj (linearInclusion g)).toMonoidHom.comp linearInclusion =
        linearInclusion.comp (MulAut.conj g).toMonoidHom := by
      apply MonoidHom.ext
      intro a
      exact conjugation_linear g a
    rw [Subgroup.map_map,hf,←Subgroup.map_map,
      ←MulAction.stabilizer_smul_eq_stabilizer_map_conj,hg]
    rfl
  have horient : ∃ (a : MulAut FieldExtension) (δ : MulAut PSL),
      ((Matrix.PSL3.RootPlaneGeometry.parabolic F b).map linearInclusion).map a.toMonoidHom =
        PairPlane.pointParabolic.map linearInclusion ∧
      ∀ g : PSL, a (linearInclusion g) = linearInclusion (δ g) := by
    cases b
    · obtain ⟨a,δ,ha,hδ⟩ := hpoint (axis 2)
      refine ⟨graphExtension.trans a,(graph F).trans δ,?_,?_⟩
      · have hf : graphExtension.toMonoidHom.comp linearInclusion =
            linearInclusion.comp (graph F).toMonoidHom := by
          apply MonoidHom.ext
          intro g
          exact graphExtension_linear g
        change ((Matrix.PSL3.LinearThree.lineParabolic F).map linearInclusion).map
          (a.toMonoidHom.comp graphExtension.toMonoidHom) = _
        rw [←Subgroup.map_map]
        have hm : ((Matrix.PSL3.LinearThree.lineParabolic F).map linearInclusion).map
            graphExtension.toMonoidHom = (MulAction.stabilizer PSL (axis 2)).map linearInclusion := by
          rw [Subgroup.map_map,hf,←Subgroup.map_map,graph_line_eq_stabilizer]
        rw [hm,ha]
      · intro g
        change a (graphExtension (linearInclusion g)) = linearInclusion (δ (graph F g))
        rw [graphExtension_linear,hδ]
    · obtain ⟨a,δ,ha,hδ⟩ := hpoint (axis 0)
      refine ⟨a,δ,?_,hδ⟩
      change ((Matrix.PSL3.LinearThree.pointParabolic F).map _).map _ = _
      rw [point_eq_stabilizer]
      exact ha
  obtain ⟨a,δ,ha,hδ⟩ := horient
  refine ⟨a.trans PairPlane.pairEquiv.symm,δ,?_,?_⟩
  · change ((Matrix.PSL3.RootPlaneGeometry.parabolic F b).map linearInclusion).map
      (PairPlane.pairEquiv.symm.toMonoidHom.comp a.toMonoidHom) = _
    rw [←Subgroup.map_map,ha]
    apply Subgroup.map_injective (f := pairStabilizer.subtype) pairStabilizer.subtype_injective
    rw [Subgroup.map_map,Subgroup.map_map]
    have hf : pairStabilizer.subtype.comp
        (PairPlane.pairEquiv.symm.toMonoidHom.comp linearInclusion) = PairPlane.pslToM23 := by
      apply MonoidHom.ext
      intro g
      exact PairPlane.fieldExtensionToM23_linear g
    rw [MonoidHom.comp_assoc,hf,PairPlane.pointParabolic_map,map_subgroupOf_eq_of_le inf_le_left]
  · intro g
    change PairPlane.pairEquiv.symm (a (linearInclusion g)) = _
    rw [hδ]
    apply PairPlane.pairEquiv.injective
    rw [PairPlane.pairEquiv.apply_symm_apply,PairPlane.pairEquiv_pointwise,
      PairPlane.pointwiseEquiv.apply_symm_apply]

end Sporadic.Mathieu.M23Geometry.SourceVertex
