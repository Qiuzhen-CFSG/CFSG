module
public import Theory.GroupAction.SymplecticRankThree.ProjectivePlane

/-!
# Ordinary field coordinates on every whole polar block

The finite-field isomorphism transports homogeneous coordinates to F³ and
preserves vector spans. The chart extends the retained affine field chart
by a leading coordinate one; its actual infinite directions are precisely
the zero-first-coordinate points. Counting gives a center outside any two
planes, so central projection transports this complete PG(2,F) chart to
every polar block. All formulas include q=2 and q=4.

These are constructed coordinates on whole planes, not yet a single
compatible coordinate map on the full projective three-space. SourcePlanes
and PlanesChapter12 apply them to the same original marked quotient.

Source: Higman (1964), Lemma 10 and Theorem 2(i), pp.153–155,
the expanded projective coordinatization step.
-/

public noncomputable section
open Projectivization
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)
local instance : DecidablePred (· ∈ D.block f.infinity) := Classical.decPred _
local instance : AddCommGroup (f.Base hl hq) := f.affineAddCommGroup hl hq
local instance : Field (f.scalarRing hl hq) := f.scalarField hl hq
local instance : Module (f.scalarRing hl hq) (f.Base hl hq) := f.scalarModule hl hq


section FieldTransport
variable (F : Type*) [Field F] [Finite F] (hcard : q = Nat.card F)
local instance : RingHomInvPair (f.scalarFieldEquiv hl hq F hcard).toRingHom
    (f.scalarFieldEquiv hl hq F hcard).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (f.scalarFieldEquiv hl hq F hcard)
local instance : RingHomInvPair (f.scalarFieldEquiv hl hq F hcard).symm.toRingHom
    (f.scalarFieldEquiv hl hq F hcard).toRingHom :=
  RingHomInvPair.of_ringEquiv (f.scalarFieldEquiv hl hq F hcard).symm

/-- Homogeneous vectors over the reconstructed field are transported to
the supplied field of the same order, using the proved finite-field isomorphism. -/
@[expose] def planeHomogeneousEquiv :
    (f.scalarRing hl hq × f.Base hl hq) ≃ₛₗ[(f.scalarFieldEquiv hl hq F hcard).toRingHom]
      F × (F × F) where
  toEquiv := ((Equiv.refl _).prodCongr (f.fieldPlaneCoordinates hl hq).toEquiv).trans
    ((f.scalarFieldEquiv hl hq F hcard).toEquiv.prodCongr
      ((f.scalarFieldEquiv hl hq F hcard).toEquiv.prodCongr
        (f.scalarFieldEquiv hl hq F hcard).toEquiv))
  map_add' u v := by
    let e := f.scalarFieldEquiv hl hq F hcard
    let C := f.fieldPlaneCoordinates hl hq
    apply Prod.ext
    · change e (u.1+v.1) = e u.1 + e v.1
      exact map_add e _ _
    · apply Prod.ext
      · change e (C (u.2+v.2)).1 = e (C u.2).1 + e (C v.2).1
        rw [map_add]
        exact map_add e _ _
      · change e (C (u.2+v.2)).2 = e (C u.2).2 + e (C v.2).2
        rw [map_add]
        exact map_add e _ _
  map_smul' r v := by
    let e := f.scalarFieldEquiv hl hq F hcard
    let C := f.fieldPlaneCoordinates hl hq
    apply Prod.ext
    · change e (r*v.1) = e r * e v.1
      exact map_mul e _ _
    · apply Prod.ext
      · change e (C (r • v.2)).1 = e r * e (C v.2).1
        rw [map_smul]
        exact map_mul e _ _
      · change e (C (r • v.2)).2 = e r * e (C v.2).2
        rw [map_smul]
        exact map_mul e _ _

@[expose] def planeProjectiveFieldEquiv :
    Projectivization (f.scalarRing hl hq) (f.scalarRing hl hq × f.Base hl hq) ≃
      Projectivization F (F × (F × F)) where
  toFun := Projectivization.map (f.planeHomogeneousEquiv hl hq F hcard).toLinearMap
    (f.planeHomogeneousEquiv hl hq F hcard).injective
  invFun := Projectivization.map (f.planeHomogeneousEquiv hl hq F hcard).symm.toLinearMap
    (f.planeHomogeneousEquiv hl hq F hcard).symm.injective
  left_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp only [map_mk,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
  right_inv p := by
    induction p using Projectivization.ind with | h v hv =>
    simp only [map_mk,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]

theorem planeProjectiveFieldEquiv_line (a b x :
    Projectivization (f.scalarRing hl hq) (f.scalarRing hl hq × f.Base hl hq)) :
    (f.planeProjectiveFieldEquiv hl hq F hcard x).submodule ≤
      (f.planeProjectiveFieldEquiv hl hq F hcard a).submodule ⊔
        (f.planeProjectiveFieldEquiv hl hq F hcard b).submodule ↔
      x.submodule ≤ a.submodule ⊔ b.submodule := by
  let e := f.scalarFieldEquiv hl hq F hcard
  let E := f.planeHomogeneousEquiv hl hq F hcard
  induction a using Projectivization.ind with | h a ha =>
  induction b using Projectivization.ind with | h b hb =>
  induction x using Projectivization.ind with | h x hx =>
  change (Projectivization.map E.toLinearMap E.injective (Projectivization.mk _ x hx)).submodule ≤
    (Projectivization.map E.toLinearMap E.injective (Projectivization.mk _ a ha)).submodule ⊔
    (Projectivization.map E.toLinearMap E.injective (Projectivization.mk _ b hb)).submodule ↔ _
  simp only [map_mk,submodule_mk,← Submodule.span_insert,Submodule.span_singleton_le_iff_mem,
    Submodule.mem_span_pair,LinearEquiv.coe_coe]
  constructor
  · rintro ⟨r,s,hrs⟩
    refine ⟨e.symm r,e.symm s,E.injective ?_⟩
    rw [map_add,E.map_smulₛₗ,E.map_smulₛₗ]
    change e (e.symm r) • E a + e (e.symm s) • E b = E x
    simpa only [e.apply_symm_apply] using hrs
  · rintro ⟨r,s,hrs⟩
    refine ⟨e r,e s,?_⟩
    have hh := congrArg E hrs
    rw [map_add,E.map_smulₛₗ,E.map_smulₛₗ] at hh
    exact hh

/-- Ordinary projective coordinates on the entire base plane, over any
specified finite field of order q. -/
@[expose] def projectivePlaneCoordinatesOver : f.Plane hl hq ≃
    Projectivization F (F × (F × F)) :=
  (f.projectivePlaneCoordinates hl hq).trans (f.planeProjectiveFieldEquiv hl hq F hcard)

theorem projectivePlaneCoordinatesOver_line (a b x : f.Plane hl hq) :
    (f.projectivePlaneCoordinatesOver hl hq F hcard x).submodule ≤
      (f.projectivePlaneCoordinatesOver hl hq F hcard a).submodule ⊔
        (f.projectivePlaneCoordinatesOver hl hq F hcard b).submodule ↔ (x : Ω) ∈ D.line a b :=
  (f.planeProjectiveFieldEquiv_line hl hq F hcard _ _ _).trans
    (f.projectivePlaneCoordinates_line hl hq a b x)

/-- The homogeneous chart literally extends the retained affine field
coordinates by adjoining a leading coordinate equal to one. -/
theorem projectivePlaneCoordinatesOver_affine (a : f.Base hl hq) :
    f.projectivePlaneCoordinatesOver hl hq F hcard ⟨a,a.property⟩ =
      Projectivization.mk F (1,f.fieldPlaneCoordinatesOver hl hq F hcard a)
        (fun hh => one_ne_zero (congrArg Prod.fst hh)) := by
  let E := f.planeHomogeneousEquiv hl hq F hcard
  change Projectivization.map E.toLinearMap E.injective
    (Projectivization.mk _ (f.planeVector hl hq ⟨a,a.property⟩) _) = _
  rw [map_mk]
  apply (mk_eq_mk_iff' _ _ _ _ _).mpr
  refine ⟨1,?_⟩
  rw [one_smul,f.planeVector_affine]
  apply Prod.ext
  · exact (map_one (f.scalarFieldEquiv hl hq F hcard)).symm
  · rfl

/-- The actual infinite directions are exactly the points with zero
leading homogeneous coordinate. -/
theorem projectivePlaneCoordinatesOver_infinity (x : f.Plane hl hq) :
    (f.projectivePlaneCoordinatesOver hl hq F hcard x).submodule ≤
      (LinearMap.fst F F (F × F)).ker ↔ (x : Ω) ∈ D.block f.infinity := by
  let E := f.planeHomogeneousEquiv hl hq F hcard
  change (Projectivization.map E.toLinearMap E.injective
    (Projectivization.mk _ (f.planeVector hl hq x) _)).submodule ≤ _ ↔ _
  rw [map_mk,submodule_mk,Submodule.span_singleton_le_iff_mem,LinearMap.mem_ker]
  change (f.scalarFieldEquiv hl hq F hcard) (f.planeVector hl hq x).1 = 0 ↔ _
  by_cases hx : (x : Ω) ∈ D.block f.infinity
  · rw [show f.planeVector hl hq x = (0,(f.axisUnit hl hq ⟨x,hx,x.property⟩).val) from
      f.planeVector_direction hl hq ⟨x,hx,x.property⟩]
    change (f.scalarFieldEquiv hl hq F hcard) 0 = 0 ↔ _
    rw [map_zero]
    exact ⟨fun _ => hx,fun _ => rfl⟩
  · rw [show f.planeVector hl hq x = (1,(⟨⟨x,hx⟩,x.property⟩ : f.Base hl hq)) from
      f.planeVector_affine hl hq ⟨⟨x,hx⟩,x.property⟩]
    change (f.scalarFieldEquiv hl hq F hcard) 1 = 0 ↔ _
    rw [map_one]
    exact ⟨fun hh => (one_ne_zero hh).elim,fun hh => (hx hh).elim⟩


end FieldTransport

end Theory.GroupAction.SymplecticRankThree.AffineFrame

namespace Theory.GroupAction.SymplecticRankThree.PolarityDesign
variable {Ω : Type*} [Finite Ω] {q : ℕ} (D : PolarityDesign Ω q)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)

include hq in
/-- There is a projection center outside any two planes, including at q=2. -/
theorem exists_point_off_two_blocks (hdegree : Nat.card Ω = q^3+q^2+q+1) (p r : Ω) :
    ∃ c, c ∉ D.block p ∧ c ∉ D.block r := by
  by_contra! hh
  have hu : D.block p ∪ D.block r = Set.univ := by
    apply Set.eq_univ_of_forall
    intro c
    by_cases hc : c ∈ D.block p
    · exact Or.inl hc
    · exact Or.inr (hh c hc)
  have hn := Set.ncard_union_le (D.block p) (D.block r)
  rw [hu,Set.ncard_univ,hdegree,
    show (D.block p).ncard = q^2+q+1 from D.block_card p,
    show (D.block r).ncard = q^2+q+1 from D.block_card r] at hn
  have h₂ : 2*q ≤ q^2 := by nlinarith [Nat.mul_le_mul_right q hq]
  have h₃ : 2*q^2 ≤ q^3 := by nlinarith [Nat.mul_le_mul_right (q^2) hq]
  nlinarith

include hl hq in
/-- Every whole polar block has ordinary projective-plane coordinates over
the same finite field. The coordinates and their line formulas are constructed
from incidence; they are not supplied as hypotheses. -/
theorem exists_projective_plane_coordinates
    (hdegree : Nat.card Ω = q^3+q^2+q+1) (p : Ω)
    (F : Type*) [Field F] [Finite F] (hcard : q = Nat.card F) :
    ∃ C : ↥(D.block p) ≃ Projectivization F (F × (F × F)),
      ∀ a b x : ↥(D.block p), (C x).submodule ≤ (C a).submodule ⊔ (C b).submodule ↔
        (x : Ω) ∈ D.line a b := by
  obtain ⟨f,_⟩ := D.exists_affineFrame hl hq hdegree p
  let r := f.level hl hq f.originPoint
  obtain ⟨c,hcp,hcr⟩ := D.exists_point_off_two_blocks hq hdegree p r
  let E := D.perspectivity hl hq p r c hcp hcr
  refine ⟨E.trans (f.projectivePlaneCoordinatesOver hl hq F hcard),?_⟩
  intro a b x
  exact (f.projectivePlaneCoordinatesOver_line hl hq F hcard (E a) (E b) (E x)).trans
    (D.perspectivity_collinear hl hq p r c hcp hcr a b x)

end Theory.GroupAction.SymplecticRankThree.PolarityDesign
