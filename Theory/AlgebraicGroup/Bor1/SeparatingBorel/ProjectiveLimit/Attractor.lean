module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.OrbitProjection

/-!
# The distinguished highest-weight point and its open basin

For a connected group's closed projective orbit with finite cocharacter fixed
locus, choose the largest weight occurring in the orbit span. Its regular
projection has finite projective image and hence a single value on its nonzero
locus. A coordinate in that line cuts out the actual projective hyperplane
complement forming the basin. The endpoint itself belongs to this basin, and
every basin point has the explicit affine curve for the original action.

Source: Borel, *Linear Algebraic Groups*, IV, 13.8; used in 13.11–13.12.
-/

public noncomputable section

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

theorem exists_attractor_in_weight_basis
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
      (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv))).Finite) :
    ∃ (M : ℤ) (j : Fin (Module.finrank k E)) (y : Point (projectiveSpace k E)),
      characterCocharacterPairing T c (Additive.ofMul (χ j)) = M ∧
      (∀ (g : Variety.Point G) i, b.equivFun ((ρ.action g).1 v) i ≠ 0 →
        characterCocharacterPairing T c (Additive.ofMul (χ i)) ≤ M) ∧
      y ∈ fixedOrbit A T c
        (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)) ∧
      y.1 (IsLocalRing.closedPoint k) ∈ projectiveHyperplaneOpen b₀ (b.coord j) ∧
      IsOpen {g : Variety.Point G |
        (A.toMulAction.smul g (projectivePointOfVector (b₀.equivFun v)
          (b₀.equivFun.map_ne_zero_iff.mpr hv))).1 (IsLocalRing.closedPoint k) ∈
            projectiveHyperplaneOpen b₀ (b.coord j)} ∧
      (∃ g : Variety.Point G,
        (A.toMulAction.smul g (projectivePointOfVector (b₀.equivFun v)
          (b₀.equivFun.map_ne_zero_iff.mpr hv))).1 (IsLocalRing.closedPoint k) ∈
            projectiveHyperplaneOpen b₀ (b.coord j)) ∧
      (∀ g : Variety.Point G,
        (A.toMulAction.smul g (projectivePointOfVector (b₀.equivFun v)
          (b₀.equivFun.map_ne_zero_iff.mpr hv))).1 (IsLocalRing.closedPoint k) ∈
            projectiveHyperplaneOpen b₀ (b.coord j) →
        ∃ f : Variety.Geometric.Morphism (polynomialAffineLine k) (projectiveSpace k E),
          f (ProjectivePolynomialCurve.affinePoint 0) = y ∧
          ∀ (a : k) (ha : a ≠ 0), f (ProjectivePolynomialCurve.affinePoint a) =
            A.toMulAction.smul
              (T.includePoint (c.onPoints (cocharacterParameter (Units.mk0 a ha)⁻¹)))
              (A.toMulAction.smul g (projectivePointOfVector (b₀.equivFun v)
                (b₀.equivFun.map_ne_zero_iff.mpr hv)))) ∧
      Module.finrank k (Submodule.span k (Set.range fun g : Variety.Point G =>
        topCoordinates (b.equivFun ((ρ.action g).1 v))
          (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M)) = 1 := by
  let m := fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))
  let x := projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)
  obtain ⟨M, hne, hM⟩ := exists_largest_orbit_weight ρ b m v hv
  obtain ⟨F, hF⟩ := exists_regular_top_coordinates ρ hρ b m M v
  have hFv (g : Variety.Point G) : (fun i => F i g) =
      topCoordinates (b.equivFun ((ρ.action g).1 v)) m M := funext (hF g)
  have hneF : ∃ g : Variety.Point G, (fun i => F i g) ≠ 0 := by
    simpa only [hFv] using hne
  let S := coordinateProjectivization b₀ b '' fixedOrbit A T c x
  have hS : S.Finite := hfinite.image _
  have himage (g : Variety.Point G) (hg : (fun i => F i g) ≠ 0) :
      Projectivization.mk k (fun i => F i g) hg ∈ S := by
    have ht : topCoordinates (b.equivFun ((ρ.action g).1 v)) m M ≠ 0 := by
      rwa [hFv] at hg
    have hp := projective_top_coordinates_mem_fixed_image ρ T c A b₀ b χ he hweight
      v hv hclosed M hM g ht
    simpa only [hFv] using hp
  obtain ⟨p, hpS, j, hopen, ⟨g₀, hg₀⟩, hiff, hconstant⟩ :=
    exists_open_constant_projective_value (connectedAlgebraicGroup_irreducible G hG)
      F S hS hneF himage
  obtain ⟨y, hy, hyp⟩ := hpS
  have hmj : m j = M := by
    by_contra hj
    apply hg₀
    rw [hF g₀ j]
    exact if_neg hj
  have hFj (g : Variety.Point G) : F j g = b.coord j ((ρ.action g).1 v) := by
    rw [hF g j]
    exact if_pos hmj
  have hUiff (g : Variety.Point G) :
      (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∈
        projectiveHyperplaneOpen b₀ (b.coord j) ↔ F j g ≠ 0 := by
    rw [action_projective_vector ρ A b₀ he g v hv]
    exact (projectiveHyperplaneOpen_vector_mem_iff b₀ (b.coord j) ((ρ.action g).1 v)
      ((ρ.action g).toLinearEquiv.map_ne_zero_iff.mpr hv)).trans (by rw [hFj g])
  have hendpoint (g : Variety.Point G)
      (htop : ∃ i, m i = M ∧ b.equivFun ((ρ.action g).1 v) i ≠ 0) :
      projectivePointOfVector (b₀.equivFun (topVector b m M ((ρ.action g).1 v)))
        (b₀.equivFun.map_ne_zero_iff.mpr (topVector_ne_zero b m M ((ρ.action g).1 v) htop)) = y := by
    have hg : (fun i => F i g) ≠ 0 := by
      rw [hFv]
      exact topCoordinates_ne_zero _ _ _ htop
    apply (coordinateProjectivization b₀ b).injective
    rw [coordinateProjectivization_vector b₀ b _ (topVector_ne_zero b m M ((ρ.action g).1 v) htop), hyp]
    change Projectivization.mk k (b.equivFun (b.equivFun.symm _)) _ = p
    simp only [LinearEquiv.apply_symm_apply]
    have hc := hconstant g hg
    simpa only [hFv] using hc
  have ht₀ : ∃ i, m i = M ∧ b.equivFun ((ρ.action g₀).1 v) i ≠ 0 := by
    refine ⟨j, hmj, ?_⟩
    change b.coord j ((ρ.action g₀).1 v) ≠ 0
    rwa [← hFj]
  refine ⟨M, j, y, hmj, hM, hy, ?_, ?_, ⟨g₀, (hUiff g₀).mpr hg₀⟩, ?_, ?_⟩
  · rw [← hendpoint g₀ ht₀]
    apply (projectiveHyperplaneOpen_vector_mem_iff b₀ (b.coord j)
      (topVector b m M ((ρ.action g₀).1 v))
      (topVector_ne_zero b m M ((ρ.action g₀).1 v) ht₀)).mpr
    change b.equivFun (b.equivFun.symm _) j ≠ 0
    rw [LinearEquiv.apply_symm_apply, ← hF g₀ j]
    exact hg₀
  · have hset : {g : Variety.Point G | (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∈
        projectiveHyperplaneOpen b₀ (b.coord j)} = {g : Variety.Point G | F j g ≠ 0} := by
      ext g
      exact hUiff g
    change IsOpen {g : Variety.Point G | (A.toMulAction.smul g x).1 (IsLocalRing.closedPoint k) ∈
      projectiveHyperplaneOpen b₀ (b.coord j)}
    rw [hset]
    exact hopen
  · intro g hg
    have ht : ∃ i, m i = M ∧ b.equivFun ((ρ.action g).1 v) i ≠ 0 := by
      refine ⟨j, hmj, ?_⟩
      change b.coord j ((ρ.action g).1 v) ≠ 0
      rw [← hFj]
      exact (hUiff g).mp hg
    refine ⟨originalTopCurve b₀ b m M ((ρ.action g).1 v) ht, ?_, ?_⟩
    · exact (originalTopCurve_zero b₀ b m M ((ρ.action g).1 v) ht (hM g)).trans (hendpoint g ht)
    · intro a ha
      have hc := originalTopCurve_nonzero ρ T c A b₀ b χ he hweight M ((ρ.action g).1 v)
        ((ρ.action g).toLinearEquiv.map_ne_zero_iff.mpr hv) ht (hM g) a ha
      exact hc.trans (congrArg (fun z : Point (projectiveSpace k E) =>
        A.toMulAction.smul (T.includePoint (c.onPoints (cocharacterParameter (Units.mk0 a ha)⁻¹))) z)
        (action_projective_vector ρ A b₀ he g v hv).symm)
  · exact finrank_top_orbit_span_eq_one ρ hρ hG T c A b₀ b χ he hweight v hv hclosed hfinite M hne hM

end Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
