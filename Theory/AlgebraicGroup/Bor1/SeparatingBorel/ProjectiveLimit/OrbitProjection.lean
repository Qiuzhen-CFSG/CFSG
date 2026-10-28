module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.ClosedInvariant
public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.FiniteImage
public import Theory.AlgebraicGroup.Representations.RationalBasis

/-!
# Highest-weight projections on the original closed orbit

The explicit cocharacter limit belongs to the original closed orbit and is
fixed there. Hence a finite fixed locus bounds the actual projective image of
the highest-weight projection of the orbit. The projected coordinates are
regular matrix coefficients, so the finite-image irreducibility theorem
applies to the original connected group.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open scoped LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit

universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {G : Variety k} [AlgebraicGroup G]

def fixedOrbit (A : MorphicAction G (projectiveSpace k E)) (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T) (x : Point (projectiveSpace k E)) :
    Set (Point (projectiveSpace k E)) :=
  {y | (∃ g : Variety.Point G, A.toMulAction.smul g x = y) ∧
    ∀ t : Variety.Point (KMult k), A.toMulAction.smul (T.includePoint (c.onPoints t)) y = y}

def coordinateProjectivization
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E) :
    Point (projectiveSpace k E) ≃ ℙ k (Fin (Module.finrank k E) → k) :=
  (projectiveSpacePointEquivOf b₀).trans (projectivizationEquivOfLinearEquiv b.equivFun)

theorem coordinateProjectivization_vector
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E) (v : E) (hv : v ≠ 0) :
    coordinateProjectivization b₀ b
        (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)) =
      Projectivization.mk k (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv) := by
  change (projectivizationEquivOfLinearEquiv b.equivFun)
    (projectiveSpacePointEquivOf b₀ (projectivePointOfVector _ _)) = _
  rw [projectiveSpacePointEquivOf_projectivePointOfVector b₀ v hv]
  exact Projectivization.map_mk b.equivFun.toLinearMap b.equivFun.injective v hv

omit [IsAlgClosed k] [FiniteDimensional k E] in
theorem topCoordinates_ne_zero_iff
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (m : Fin (Module.finrank k E) → ℤ) (M : ℤ) (v : E) :
    topCoordinates (b.equivFun v) m M ≠ 0 ↔
      ∃ i, m i = M ∧ b.equivFun v i ≠ 0 := by
  classical
  constructor
  · intro hv
    obtain ⟨i, hi⟩ : ∃ i, topCoordinates (b.equivFun v) m M i ≠ 0 := by
      simpa only [Function.ne_iff, Pi.zero_apply] using hv
    by_cases hm : m i = M
    · exact ⟨i, hm, by simpa only [topCoordinates, if_pos hm] using hi⟩
    · simp only [topCoordinates, if_neg hm, ne_eq, not_true_eq_false] at hi
  · exact topCoordinates_ne_zero _ _ _

/-- The projection lies in the actual cocharacter-fixed locus of the original
closed orbit. -/
theorem topVector_mem_fixedOrbit
    (ρ : RationalRepresentation G E) (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T)
    (A : MorphicAction G (projectiveSpace k E))
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E)
    (χ : Fin (Module.finrank k E) → TorusWeight T)
    (he : ∀ g p, projectiveSpacePointEquivOf b₀ (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b₀ p))
    (hweight : ∀ i t, (ρ.action (T.includePoint t)).1 (b i) =
      (χ i).pointCharacter t • b i)
    (x : Point (projectiveSpace k E))
    (hclosed : IsClosed (Set.range (A.orbitMorphismAt x).hom))
    (M : ℤ) (v : E) (hv : v ≠ 0)
    (h : ∃ i, characterCocharacterPairing T c (Additive.ofMul (χ i)) = M ∧ b.equivFun v i ≠ 0)
    (hM : ∀ i, b.equivFun v i ≠ 0 → characterCocharacterPairing T c (Additive.ofMul (χ i)) ≤ M)
    (hx : ∃ g : Variety.Point G, A.toMulAction.smul g x =
      projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)) :
    projectivePointOfVector
      (b₀.equivFun (topVector b (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M v))
      (b₀.equivFun.map_ne_zero_iff.mpr (topVector_ne_zero b _ M v h)) ∈ fixedOrbit A T c x := by
  refine ⟨?_, topVector_projective_fixed ρ T c A b₀ b χ he hweight M v h⟩
  apply (A.point_mem_orbit_range_iff x _).mp
  apply topVector_mem_closed_invariant ρ T c A b₀ b χ he hweight M v hv h hM hclosed
  · intro t p hp
    obtain ⟨g, rfl⟩ := (A.point_mem_orbit_range_iff x p).mp hp
    exact (A.point_mem_orbit_range_iff x _).mpr
      ⟨T.includePoint (c.onPoints t) * g, A.toMulAction.mul_smul _ _ _⟩
  · exact (A.point_mem_orbit_range_iff x _).mpr hx

/-- The actual projected orbit coordinates are polynomial functions of the
original group element. -/
theorem exists_regular_top_coordinates
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (m : Fin (Module.finrank k E) → ℤ) (M : ℤ) (v : E) :
    ∃ F : Fin (Module.finrank k E) → G.PolynomialFunction,
      ∀ (g : Variety.Point G) (i : Fin (Module.finrank k E)),
        F i g = topCoordinates (b.equivFun ((ρ.action g).1 v)) m M i := by
  classical
  obtain ⟨e, φ, hφ⟩ := hρ
  let C := fun i => rationalRepresentationLinearMatrixCoefficient ρ e φ (b.coord i) v
  refine ⟨fun i => if m i = M then C i else 0, ?_⟩
  intro g i
  by_cases hi : m i = M
  · simp only [if_pos hi, topCoordinates]
    exact rationalRepresentationLinearMatrixCoefficient_apply ρ e φ hφ (b.coord i) v g
  · simp only [if_neg hi, topCoordinates]
    rfl

theorem projective_top_coordinates_mem_fixed_image
    (ρ : RationalRepresentation G E) (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T)
    (A : MorphicAction G (projectiveSpace k E))
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E)
    (χ : Fin (Module.finrank k E) → TorusWeight T)
    (he : ∀ g p, projectiveSpacePointEquivOf b₀ (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b₀ p))
    (hweight : ∀ i t, (ρ.action (T.includePoint t)).1 (b i) =
      (χ i).pointCharacter t • b i)
    (v : E) (hv : v ≠ 0)
    (hclosed : IsClosed (Set.range (A.orbitMorphismAt
      (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv))).hom))
    (M : ℤ)
    (hM : ∀ (g : Variety.Point G) i, b.equivFun ((ρ.action g).1 v) i ≠ 0 →
      characterCocharacterPairing T c (Additive.ofMul (χ i)) ≤ M)
    (g : Variety.Point G)
    (hw : topCoordinates (b.equivFun ((ρ.action g).1 v))
      (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M ≠ 0) :
    Projectivization.mk k
      (topCoordinates (b.equivFun ((ρ.action g).1 v))
        (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M) hw ∈
      coordinateProjectivization b₀ b '' fixedOrbit A T c
        (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)) := by
  let m := fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))
  have htop := (topCoordinates_ne_zero_iff b m M ((ρ.action g).1 v)).mp hw
  let w := topVector b m M ((ρ.action g).1 v)
  have hw' : w ≠ 0 := topVector_ne_zero b m M ((ρ.action g).1 v) htop
  refine ⟨projectivePointOfVector (b₀.equivFun w) (b₀.equivFun.map_ne_zero_iff.mpr hw'), ?_, ?_⟩
  · exact topVector_mem_fixedOrbit ρ T c A b₀ b χ he hweight _ hclosed M ((ρ.action g).1 v)
      ((ρ.action g).toLinearEquiv.map_ne_zero_iff.mpr hv) htop (hM g)
      ⟨g, action_projective_vector ρ A b₀ he g v hv⟩
  · rw [coordinateProjectivization_vector b₀ b w hw']
    change Projectivization.mk k (b.equivFun (b.equivFun.symm _)) _ = _
    simp only [LinearEquiv.apply_symm_apply]
    rfl

omit [IsAlgClosed k] [FiniteDimensional k E] in
/-- Choose the largest weight which occurs anywhere in the original orbit. -/
theorem exists_largest_orbit_weight
    (ρ : RationalRepresentation G E)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (m : Fin (Module.finrank k E) → ℤ) (v : E) (hv : v ≠ 0) :
    ∃ M : ℤ,
      (∃ g : Variety.Point G, topCoordinates (b.equivFun ((ρ.action g).1 v)) m M ≠ 0) ∧
      ∀ (g : Variety.Point G) i, b.equivFun ((ρ.action g).1 v) i ≠ 0 → m i ≤ M := by
  classical
  let s := Finset.univ.filter (fun i => ∃ g : Variety.Point G, b.equivFun ((ρ.action g).1 v) i ≠ 0)
  have hs : s.Nonempty := by
    have hn : b.equivFun ((ρ.action 1).1 v) ≠ 0 :=
      b.equivFun.map_ne_zero_iff.mpr ((ρ.action 1).toLinearEquiv.map_ne_zero_iff.mpr hv)
    obtain ⟨i, hi⟩ : ∃ i, b.equivFun ((ρ.action 1).1 v) i ≠ 0 := by
      simpa only [Function.ne_iff, Pi.zero_apply] using hn
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, 1, hi⟩⟩
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image m hs
  obtain ⟨g, hg⟩ := (Finset.mem_filter.mp hi).2
  refine ⟨m i, ⟨g, topCoordinates_ne_zero _ _ _ ⟨i, rfl, hg⟩⟩, ?_⟩
  intro g j hj
  exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, g, hj⟩)

/-- Source 13.8: the largest cocharacter-weight part of the span of the
original orbit is one-dimensional when the original fixed locus is finite. -/
theorem finrank_top_orbit_span_eq_one
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (hG : Variety.IsConnected G) (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T)
    (A : MorphicAction G (projectiveSpace k E))
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E)
    (χ : Fin (Module.finrank k E) → TorusWeight T)
    (he : ∀ g p, projectiveSpacePointEquivOf b₀ (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b₀ p))
    (hweight : ∀ i t, (ρ.action (T.includePoint t)).1 (b i) =
      (χ i).pointCharacter t • b i)
    (v : E) (hv : v ≠ 0)
    (hclosed : IsClosed (Set.range (A.orbitMorphismAt
      (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv))).hom))
    (hfinite : (fixedOrbit A T c
      (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv))).Finite)
    (M : ℤ)
    (hne : ∃ g : Variety.Point G, topCoordinates (b.equivFun ((ρ.action g).1 v))
      (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M ≠ 0)
    (hM : ∀ (g : Variety.Point G) i, b.equivFun ((ρ.action g).1 v) i ≠ 0 →
      characterCocharacterPairing T c (Additive.ofMul (χ i)) ≤ M) :
    Module.finrank k (Submodule.span k (Set.range fun g : Variety.Point G =>
      topCoordinates (b.equivFun ((ρ.action g).1 v))
        (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M)) = 1 := by
  let m := fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))
  obtain ⟨F, hF⟩ := exists_regular_top_coordinates ρ hρ b m M v
  have hFv (g : Variety.Point G) : (fun i => F i g) =
      topCoordinates (b.equivFun ((ρ.action g).1 v)) m M := funext (hF g)
  have hneF : ∃ g : Variety.Point G, (fun i => F i g) ≠ 0 := by
    simpa only [hFv] using hne
  let S := coordinateProjectivization b₀ b '' fixedOrbit A T c
    (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv))
  have hS : S.Finite := hfinite.image _
  have himage (g : Variety.Point G) (hg : (fun i => F i g) ≠ 0) :
      Projectivization.mk k (fun i => F i g) hg ∈ S := by
    have ht : topCoordinates (b.equivFun ((ρ.action g).1 v)) m M ≠ 0 := by
      rwa [hFv] at hg
    have hp := projective_top_coordinates_mem_fixed_image ρ T c A b₀ b χ he hweight
      v hv hclosed M hM g ht
    simpa only [hFv] using hp
  have hdim := finrank_span_eq_one_of_finite_projective_image
    (connectedAlgebraicGroup_irreducible G hG) F S hS hneF himage
  have hfun : (fun g i => F i g) =
      (fun g => topCoordinates (b.equivFun ((ρ.action g).1 v)) m M) := funext hFv
  rw [hfun] at hdim
  exact hdim

end Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
