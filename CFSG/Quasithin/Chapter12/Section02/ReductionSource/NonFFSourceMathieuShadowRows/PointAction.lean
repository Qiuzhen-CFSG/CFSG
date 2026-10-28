module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.PointComponent
public import CFSG.Quasithin.Chapter8.Section01.MathieuShadowRows.SectionControl

/-!
# The full original M22 cocode point action

Restrict the full automizer marking to an original point subgroup. The
compatible native inner/outer identifications give its action on the actual
field extension of PSL₃(4). Its entire kernel centralizes the original orbit,
and the image of the original point residual is exactly the linear subgroup.
Consequently its section centralizer centralizes the original whole orbit.

Source: Aschbacher--Smith H.15.1, A.4.2.7 and 8.1.1, pp.398,57,712.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- Restrict the full original action without replacing the point subgroup
by its image or dropping any part of the covering kernel. -/
theorem sourceOrbit_m22_cocode_point_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation)
    (x : D.sourceOrbit) (i : Fin 22)
    (hx : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul x) = m22WeightTwoVector i)
    (A : Subgroup G) (hAN : A ≤ normalizer (D.sourceOrbit : Set G))
    (hAH : A ≤ centralizer ({(x : G)} : Set G))
    (hCA : L ⊓ centralizer ({(x : G)} : Set G) ≤ A) :
    ∃ f : A →* Matrix.PSL3Four.FieldExtension,
      f.ker = (centralizer (D.sourceOrbit : Set G)).subgroupOf A ∧
      ((solvableResidual (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
        (inclusion hCA)).map f = Matrix.PSL3Four.linearInclusion.range := by
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
  obtain ⟨a,ha,hE,haL,_,_⟩ := D.sourceOrbit_m22_cocode_full_automizer h d
  let r := (a.comp D.sourceOrbit.normalizerMonoidHom.rangeRestrict).comp (inclusion hAN)
  have hr (c : A) : r c ∈ m22CocodeStabilizer m22OuterCocodeRepresentation
      (m22WeightTwoVector i) := by
    change m22OuterCocodeRepresentation (r c) (m22WeightTwoVector i) = m22WeightTwoVector i
    rw [←hx]
    change m22OuterCocodeRepresentation
      (a (D.sourceOrbit.normalizerMonoidHom.rangeRestrict (inclusion hAN c)))
        (E (Additive.ofMul x)) = E (Additive.ofMul x)
    rw [←hE]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    change (c : G) * (x : G) * (c : G)⁻¹ = (x : G)
    rw [mul_inv_eq_iff_eq_mul]
    exact mem_centralizer_singleton_iff.mp (hAH c.property)
  let s := r.codRestrict _ hr
  let e := m22WeightTwoVector_outer_stabilizer_equiv i
  let f := e.toMonoidHom.comp s
  refine ⟨f,?_,?_⟩
  · have hs : s.ker = r.ker := by
      ext c
      change s c = 1 ↔ r c = 1
      exact Subtype.ext_iff
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,hs]
    change ((a.comp D.sourceOrbit.normalizerMonoidHom.rangeRestrict).comp
      (inclusion hAN)).ker = _
    rw [←MonoidHom.comap_ker,D.sourceOrbit_m22_full_marking_kernel a ha]
    rfl
  · obtain ⟨fL,hfL,hcomm,_,_⟩ := D.sourceOrbit_m22_cocode_point_residual d x i hx
    have he (c : (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)) :
        f (inclusion hCA c) = Matrix.PSL3Four.linearInclusion (fL c) := by
      have hh := NormalizedShadowRows.m22_point_marking_compatible i
        ((m22WeightTwoVector_stabilizer_equiv i).symm (fL c)) (s (inclusion hCA c)) (by
          change r (inclusion hCA c) = _
          rw [hcomm]
          exact haL ⟨c.val,c.property.1⟩)
      rwa [MulEquiv.apply_symm_apply] at hh
    have hf : f.comp (inclusion hCA) = Matrix.PSL3Four.linearInclusion.comp fL :=
      MonoidHom.ext he
    rw [map_map,hf,←map_map,map_solvableResidual_eq fL hfL,solvableResidual_eq_top,
      ←MonoidHom.range_eq_map]

/-- The actual local section centralizer acts trivially on the whole original
orbit. All native full-image and covering-kernel premises are discharged. -/
theorem sourceOrbit_m22_cocode_point_section_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation)
    (x : D.sourceOrbit) (i : Fin 22)
    (hx : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul x) = m22WeightTwoVector i) :
    let H := centralizer ({(x : G)} : Set G)
    let A := H ⊓ normalizer (L : Set G)
    let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ChapterA.Section04.twoSectionCentralizer B A ≤ centralizer (D.sourceOrbit : Set G) := by
  let H := centralizer ({(x : G)} : Set G)
  let A := H ⊓ normalizer (L : Set G)
  let C := L ⊓ H
  let B := (solvableResidual C).map C.subtype
  have hx1 : (x : G) ≠ 1 := by
    intro he
    apply m22WeightTwoVector_ne_zero i
    rw [←hx,show x = 1 from Subtype.ext he]
    exact LinearEquiv.map_zero _
  have hAN : A ≤ normalizer (D.sourceOrbit : Set G) := by
    change H ⊓ normalizer (L : Set G) ≤ _
    rw [inf_comm]
    exact inf_elementCentralizer_le_normalizer_of_trivial_intersections
      (D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV).ti x.property hx1
  have hCA : C ≤ A := le_inf inf_le_right (inf_le_left.trans L.le_normalizer)
  have hBA : B ≤ A := (map_subtype_le _).trans hCA
  have hAB : A ≤ normalizer (B : Set G) :=
    ((le_inf inf_le_right (inf_le_left.trans H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
  obtain ⟨f,hker,himage⟩ := D.sourceOrbit_m22_cocode_point_action h.toHypothesis1221 d x i hx
    A hAN inf_le_left hCA
  have he : (B.subgroupOf A).map f = Matrix.PSL3Four.linearInclusion.range := by
    have hh : B.subgroupOf A = (solvableResidual C).map (inclusion hCA) := by
      apply map_injective A.subtype_injective
      rw [map_subgroupOf_eq_of_le hBA,map_map]
      rfl
    rw [hh]
    exact himage
  have hs := Chapter8.MathieuShadowRows.m22_point_section_le_kernel hBA hAB f he
  rw [hker] at hs
  exact hs.trans (by
    rintro g ⟨a,ha,rfl⟩
    exact ha)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
