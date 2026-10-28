module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.ReducedKernel
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Simplicity.Geometry
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.DerivedBound

/-!
# Singular transitivity from the monomial stabilizer and a sextet

The Omega stabilizer of a nonzero singular vector fixes no other singular
vector: six explicit Siegel transformations verify this at a coordinate
vector, and transitivity transports the assertion. Primitivity makes that
stabilizer maximal in Omega.

If a subgroup of the full orthogonal group contains this stabilizer and moves
the vector, its intersection with the normal subgroup Omega must be Omega.
Otherwise the intersection is the stabilizer, and conjugation forces the moved
vector to be another fixed point of that stabilizer.

Applied to the literal reduced integral action, a nonmonomial centralizer
element supplies the move, by the exact axis-class stabilizer theorem.
The monomial stabilizer inclusion remains an explicit premise; this module
does not assert that its lifts have already been constructed.

Source: Aschbacher, *Sporadic Groups* (1994), 25.3 and 25.5, pp.133–134.
This uses the proved primitive action on the exact binary split-eight space
to replace the source's three-orbit counting step.
-/

open Theory.AlgebraicGroup ClassicalOrthogonal ClassicalOrthogonal.Quadratic
open ClassicalOrthogonal.BinaryEightObstruction.Simplicity
public noncomputable section

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.Realization.OmegaImage.LatticeModel.SingularOrbit

private theorem base_fixed (w : V) (hw : w ≠ 0)
    (he : ∀ j : Fin 4, j ≠ 0 → siegel Q (e 0) (e j) w = w)
    (hf : ∀ j : Fin 4, j ≠ 0 → siegel Q (e 0) (f j) w = w) :
    w = e 0 := by
  have h0 : w (.inr 0) = 0 := by
    have h := congrFun (he 1 (by decide)) (.inl 1)
    simp only [siegel, polarD_e, formD_e] at h
    simpa [ClassicalOrthogonal.e] using h
  have heq (j : Fin 4) (hj : j ≠ 0) : w (.inl j) = 0 := by
    have h := congrFun (hf j hj) (.inl 0)
    simp only [siegel, polarD_e, polarD_f, formD_f] at h
    simpa [ClassicalOrthogonal.e, f, hj, Ne.symm hj] using h
  have hfq (j : Fin 4) (hj : j ≠ 0) : w (.inr j) = 0 := by
    have h := congrFun (he j hj) (.inl 0)
    simp only [siegel, polarD_e, formD_e] at h
    simpa [ClassicalOrthogonal.e, hj, Ne.symm hj] using h
  have h1 : w (.inl 0) = 1 := by
    have hn : w (.inl 0) ≠ 0 := by
      intro hz
      apply hw
      funext a
      rcases a with j | j
      · by_cases hj : j = 0
        · subst j; exact hz
        · exact heq j hj
      · by_cases hj : j = 0
        · subst j; exact h0
        · exact hfq j hj
    exact (show ∀ b : ZMod 2, b ≠ 0 → b = 1 by decide) _ hn
  funext a
  rcases a with j | j
  · by_cases hj : j = 0
    · subst j; simpa [ClassicalOrthogonal.e] using h1
    · simpa [ClassicalOrthogonal.e, hj] using heq j hj
  · by_cases hj : j = 0
    · subst j; simpa [ClassicalOrthogonal.e] using h0
    · simpa [ClassicalOrthogonal.e] using hfq j hj




private theorem fixed_base (q : Point)
    (hf : ∀ a : E, a • pointE 0 = pointE 0 → a • q = q) : q = pointE 0 := by
  apply Subtype.ext
  apply base_fixed q.val q.prop.1
  · intro j hj
    have hp : Q.polarBilin (e 0) (e j) = 0 := by rw [polarD_e]; simp [ClassicalOrthogonal.e]
    have h := hf (root (e 0) (e j) (formD_e 0) hp)
      (Subtype.ext (siegel_fix Q (e 0) (e j) (formD_e 0) hp))
    exact congrArg Subtype.val h
  · intro j hj
    have hp : Q.polarBilin (e 0) (f j) = 0 := by rw [polarD_f]; simp [ClassicalOrthogonal.e, hj]
    have h := hf (root (e 0) (f j) (formD_e 0) hp)
      (Subtype.ext (siegel_fix Q (e 0) (f j) (formD_e 0) hp))
    exact congrArg Subtype.val h

theorem stabilizer_fixed_point_unique (p q : Point)
    (hf : ∀ a : E, a • p = p → a • q = q) : q = p := by
  let := singular_pretransitive
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E (pointE 0) p
  have hh : g⁻¹ • q = pointE 0 := by
    apply fixed_base
    intro a ha
    have hc : (g * a * g⁻¹) • p = p := by
      rw [← hg]
      simp only [mul_smul, inv_smul_smul, ha]
    have h := congrArg (fun z : Point => g⁻¹ • z) (hf (g * a * g⁻¹) hc)
    simpa only [mul_smul, inv_smul_smul] using h
  have h := congrArg (fun z : Point => g • z) hh
  simpa only [smul_inv_smul, hg] using h

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.Realization.OmegaImage.LatticeModel.SingularOrbit

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization.OmegaImage.LatticeModel

theorem omega_le_of_stabilizer_and_mover
    (R : Subgroup SelectedGeometry.Orthogonal)
    (v : SelectedGeometry.Space) (hv0 : v ≠ 0) (hv : SelectedGeometry.form v = 0)
    (hStab : ∀ a : SelectedGeometry.omega, a.val.val v = v → a.val ∈ R)
    (hMove : ∃ r : R, r.val.val v ≠ v) : SelectedGeometry.omega ≤ R := by
  let p : Point := ⟨v, hv0, hv⟩
  let K : Subgroup E := R.comap SelectedGeometry.omega.subtype
  let := singular_preprimitive
  let : Nontrivial Point := ⟨⟨pointE 0, pointE 1, by decide +kernel⟩⟩
  have hHK : MulAction.stabilizer E p ≤ K := by
    intro a ha
    exact hStab a (congrArg Subtype.val ha)
  have hmax := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive E p
  rcases hmax.le_iff.mp hHK with hK | hK
  · intro a ha
    exact (show (⟨a, ha⟩ : E) ∈ K from hK ▸ Subgroup.mem_top _)
  · obtain ⟨r, hr⟩ := hMove
    let q : Point := ⟨r.val.val v,
      fun h => hv0 (r.val.val.injective (h.trans (map_zero _).symm)),
      ((mem_quadraticIsometrySubgroup _ _).mp r.val.prop v).trans hv⟩
    have hq : q = p := by
      apply Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction.Realization.OmegaImage.LatticeModel.SingularOrbit.stabilizer_fixed_point_unique
      intro a ha
      have haR : a.val ∈ R := hStab a (congrArg Subtype.val ha)
      have hkN : r.val⁻¹ * a.val * r.val ∈ SelectedGeometry.omega := by
        simpa only [inv_inv] using
          (inferInstance : SelectedGeometry.omega.Normal).conj_mem a.val a.prop r.val⁻¹
      let k : E := ⟨r.val⁻¹ * a.val * r.val, hkN⟩
      have hkR : k ∈ K := R.mul_mem (R.mul_mem (R.inv_mem r.prop) haR) r.prop
      have hkp : k • p = p := show k ∈ MulAction.stabilizer E p from hK ▸ hkR
      have hh := congrArg (fun z : SelectedGeometry.Space => r.val.val z)
        (congrArg Subtype.val hkp)
      change r.val.val (r.val.val.symm (a.val.val (r.val.val v))) = r.val.val v at hh
      rw [LinearEquiv.apply_symm_apply] at hh
      exact Subtype.ext hh
    exact False.elim (hr (congrArg Subtype.val hq))

theorem singular_orbit_of_stabilizer_and_escape
    (C : Coordinates) (i : Coordinate)
    (hStab : ∀ a : SelectedGeometry.omega,
      a.val.val (C.coordinates (reduction (axis i))) = C.coordinates (reduction (axis i)) →
        a.val ∈ C.orthogonalAction.range)
    (hEscape : ∃ g : centralizer, g.val ∉ Atlas.Lattices.monomialSubgroup)
    (w : SelectedGeometry.Space) (hw0 : w ≠ 0) (hw : SelectedGeometry.form w = 0) :
    ∃ g : centralizer,
      (C.orthogonalAction g).val (C.coordinates (reduction (axis i))) = w := by
  have hMove : ∃ r : C.orthogonalAction.range,
      r.val.val (C.coordinates (reduction (axis i))) ≠ C.coordinates (reduction (axis i)) := by
    obtain ⟨g, hg⟩ := hEscape
    refine ⟨C.orthogonalAction.rangeRestrict g, ?_⟩
    intro he
    apply hg
    apply (fixes_axis_class_iff_monomial g i).mp
    apply C.coordinates.injective
    change (C.orthogonalAction g).val (C.coordinates (reduction (axis i))) =
      C.coordinates (reduction (axis i)) at he
    rw [C.orthogonalAction_reduction] at he
    exact he
  have hle := omega_le_of_stabilizer_and_mover C.orthogonalAction.range
    (C.coordinates (reduction (axis i))) (C.axis_ne_zero i) (C.axis_singular i) hStab hMove
  let p : Point := ⟨C.coordinates (reduction (axis i)), C.axis_ne_zero i, C.axis_singular i⟩
  let q : Point := ⟨w, hw0, hw⟩
  let := singular_pretransitive
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq E p q
  obtain ⟨g, hg⟩ := hle a.prop
  refine ⟨g, ?_⟩
  rw [hg]
  exact congrArg Subtype.val ha

end Realization.OmegaImage.LatticeModel
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction


