module

public import Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit.BasisChange
public import Theory.AlgebraicGroup.Representations.Algebraic.TorusWeightBasis
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.OrbitEscape

/-!
# Cocharacter curves for the original projective action

The polynomial highest-weight curve is transported from an actual torus weight
basis to the original projective model. Its nonzero values are the original
cocharacter action, and its endpoint belongs to every closed invariant subset
containing the original point. No action, quotient or stabilizer is replaced.

Source: Borel, *Linear Algebraic Groups*, IV, 13.3 and 13.8.
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

def cocharacterParameter (a : kˣ) : Variety.Point (KMult k) :=
  (dPointEquiv 1).symm (fun _ => a)

def topVector (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (m : Fin (Module.finrank k E) → ℤ) (M : ℤ) (v : E) : E :=
  b.equivFun.symm (topCoordinates (b.equivFun v) m M)

omit [IsAlgClosed k] [FiniteDimensional k E] in
theorem topVector_ne_zero (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (m : Fin (Module.finrank k E) → ℤ) (M : ℤ) (v : E)
    (h : ∃ i, m i = M ∧ b.equivFun v i ≠ 0) : topVector b m M v ≠ 0 :=
  b.equivFun.symm.map_ne_zero_iff.mpr (topCoordinates_ne_zero _ _ _ h)

def originalTopCurve
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E)
    (m : Fin (Module.finrank k E) → ℤ) (M : ℤ) (v : E)
    (h : ∃ i, m i = M ∧ b.equivFun v i ≠ 0) :
    Variety.Geometric.Morphism (polynomialAffineLine k) (projectiveSpace k E) :=
  (topCurve (b.equivFun v) m M h).comp (projectiveBasisChange b₀ b)

theorem originalTopCurve_zero
    (b₀ b : Module.Basis (Fin (Module.finrank k E)) k E)
    (m : Fin (Module.finrank k E) → ℤ) (M : ℤ) (v : E)
    (h : ∃ i, m i = M ∧ b.equivFun v i ≠ 0)
    (hM : ∀ i, b.equivFun v i ≠ 0 → m i ≤ M) :
    originalTopCurve b₀ b m M v h (ProjectivePolynomialCurve.affinePoint 0) =
      projectivePointOfVector (b₀.equivFun (topVector b m M v))
        (b₀.equivFun.map_ne_zero_iff.mpr (topVector_ne_zero b m M v h)) := by
  exact (congrArg (fun p : Point (projectiveSpace k E) => projectiveBasisChange b₀ b p)
    (topCurve_zero (b.equivFun v) m M h hM)).trans
    (projectiveBasisChange_coordinates b₀ b _ _)

theorem action_projective_vector
    (ρ : RationalRepresentation G E)
    (A : MorphicAction G (projectiveSpace k E))
    (b₀ : Module.Basis (Fin (Module.finrank k E)) k E)
    (he : ∀ g p, projectiveSpacePointEquivOf b₀ (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b₀ p))
    (g : Variety.Point G) (v : E) (hv : v ≠ 0) :
    A.toMulAction.smul g
        (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)) =
      projectivePointOfVector (b₀.equivFun ((ρ.action g).1 v))
        (b₀.equivFun.map_ne_zero_iff.mpr ((ρ.action g).toLinearEquiv.map_ne_zero_iff.mpr hv)) := by
  apply (projectiveSpacePointEquivOf b₀).injective
  rw [he, projectiveSpacePointEquivOf_projectivePointOfVector b₀ v hv,
    projectiveSpacePointEquivOf_projectivePointOfVector b₀ ((ρ.action g).1 v)
      ((ρ.action g).toLinearEquiv.map_ne_zero_iff.mpr hv), Projectivization.map_mk]

omit [FiniteDimensional k E] in
theorem cocharacter_weight_coordinates
    (ρ : RationalRepresentation G E) (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (χ : Fin (Module.finrank k E) → TorusWeight T)
    (hweight : ∀ i t, (ρ.action (T.includePoint t)).1 (b i) =
      (χ i).pointCharacter t • b i)
    (a : kˣ) (v : E) :
    b.equivFun ((ρ.action (T.includePoint (c.onPoints (cocharacterParameter a)))).1 v) =
      fun i => b.equivFun v i * (a : k) ^ characterCocharacterPairing T c (Additive.ofMul (χ i)) := by
  funext i
  rw [torus_weight_basis_coordinates ρ T b χ hweight,
    characterCocharacterPairing_spec T (χ i) c]
  simp only [cocharacterParameter, Equiv.apply_symm_apply]
  exact mul_comm _ _

set_option backward.isDefEq.respectTransparency false in
theorem originalTopCurve_nonzero
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
    (M : ℤ) (v : E) (hv : v ≠ 0)
    (h : ∃ i, characterCocharacterPairing T c (Additive.ofMul (χ i)) = M ∧ b.equivFun v i ≠ 0)
    (hM : ∀ i, b.equivFun v i ≠ 0 → characterCocharacterPairing T c (Additive.ofMul (χ i)) ≤ M)
    (a : k) (ha : a ≠ 0) :
    originalTopCurve b₀ b (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i)))
        M v h (ProjectivePolynomialCurve.affinePoint a) =
      A.toMulAction.smul
        (T.includePoint (c.onPoints (cocharacterParameter (Units.mk0 a ha)⁻¹)))
        (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)) := by
  let m := fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))
  let g := T.includePoint (c.onPoints (cocharacterParameter (Units.mk0 a ha)⁻¹))
  obtain ⟨hw, hcurve⟩ := topCurve_point_nonzero (b.equivFun v) m M h hM a ha
  have hcoords : b.equivFun ((ρ.action g).1 v) =
      fun i => b.equivFun v i * (a⁻¹) ^ m i := by
    simpa only [Units.val_inv_eq_inv_val, Units.val_mk0] using
      cocharacter_weight_coordinates ρ T c b χ hweight (Units.mk0 a ha)⁻¹ v
  have hp : projectivePointOfVector _ hw =
      projectivePointOfVector (b.equivFun ((ρ.action g).1 v))
        (b.equivFun.map_ne_zero_iff.mpr ((ρ.action g).toLinearEquiv.map_ne_zero_iff.mpr hv)) := by
    apply (projectivePointOfVector_eq_iff_mk_eq _ _ _ _).mpr
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
    exact ⟨1, by simpa only [one_smul] using hcoords⟩
  exact (congrArg (fun p : Point (projectiveSpace k E) => projectiveBasisChange b₀ b p) hcurve).trans
    ((congrArg (fun p : Point (projectiveSpace k E) => projectiveBasisChange b₀ b p) hp).trans
      ((projectiveBasisChange_vector b₀ b ((ρ.action g).1 v)
        ((ρ.action g).toLinearEquiv.map_ne_zero_iff.mpr hv)).trans
        (action_projective_vector ρ A b₀ he g v hv).symm))

omit [IsAlgClosed k] [FiniteDimensional k E] in
/-- Every nonzero vector has a largest occupied weight. -/
theorem exists_largest_occupied_weight
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (m : Fin (Module.finrank k E) → ℤ) (v : E) (hv : v ≠ 0) :
    ∃ M : ℤ, (∃ i, m i = M ∧ b.equivFun v i ≠ 0) ∧
      ∀ i, b.equivFun v i ≠ 0 → m i ≤ M := by
  classical
  let s := Finset.univ.filter (fun i => b.equivFun v i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ : ∃ i, b.equivFun v i ≠ 0 := by
      simpa only [Function.ne_iff, Pi.zero_apply] using b.equivFun.map_ne_zero_iff.mpr hv
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image m hs
  refine ⟨m i, ⟨i, rfl, (Finset.mem_filter.mp hi).2⟩, ?_⟩
  intro j hj
  exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

omit [FiniteDimensional k E] in
/-- The largest-weight part is an eigenvector of the actual cocharacter. -/
theorem topVector_cocharacter_eigen
    (ρ : RationalRepresentation G E) (T : ClosedSubgroup G)
    (c : ClosedSubgroupTorusCocharacter T)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (χ : Fin (Module.finrank k E) → TorusWeight T)
    (hweight : ∀ i t, (ρ.action (T.includePoint t)).1 (b i) =
      (χ i).pointCharacter t • b i)
    (M : ℤ) (v : E) (t : Variety.Point (KMult k)) :
    (ρ.action (T.includePoint (c.onPoints t))).1
        (topVector b (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M v) =
      (dPointEquiv 1 t 0 : k) ^ M •
        topVector b (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M v := by
  apply b.equivFun.injective
  funext i
  rw [torus_weight_basis_coordinates ρ T b χ hweight,
    characterCocharacterPairing_spec T (χ i) c, map_smul]
  simp only [topVector, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul,
    topCoordinates]
  split_ifs with hi <;> simp [hi]

/-- The original projective point of the largest-weight part is fixed by the
original cocharacter action. -/
theorem topVector_projective_fixed
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
    (M : ℤ) (v : E)
    (h : ∃ i, characterCocharacterPairing T c (Additive.ofMul (χ i)) = M ∧ b.equivFun v i ≠ 0)
    (t : Variety.Point (KMult k)) :
    A.toMulAction.smul (T.includePoint (c.onPoints t))
        (projectivePointOfVector
          (b₀.equivFun (topVector b (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M v))
          (b₀.equivFun.map_ne_zero_iff.mpr (topVector_ne_zero b _ M v h))) =
      projectivePointOfVector
        (b₀.equivFun (topVector b (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M v))
        (b₀.equivFun.map_ne_zero_iff.mpr (topVector_ne_zero b _ M v h)) := by
  apply (projectiveSpacePointEquivOf b₀).injective
  rw [he, projectiveSpacePointEquivOf_projectivePointOfVector b₀ _ (topVector_ne_zero b _ M v h),
    Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  exact ⟨(dPointEquiv 1 t 0 : k) ^ M, (topVector_cocharacter_eigen ρ T c b χ hweight M v t).symm⟩

/-- The actual polynomial cocharacter curve specializes inside every closed
invariant subset of the original projective model. -/
theorem topVector_mem_closed_invariant
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
    (M : ℤ) (v : E) (hv : v ≠ 0)
    (h : ∃ i, characterCocharacterPairing T c (Additive.ofMul (χ i)) = M ∧ b.equivFun v i ≠ 0)
    (hM : ∀ i, b.equivFun v i ≠ 0 → characterCocharacterPairing T c (Additive.ofMul (χ i)) ≤ M)
    {Z : Set (projectiveSpace k E).toScheme} (hZ : IsClosed Z)
    (hinv : ∀ (t : Variety.Point (KMult k)) (p : Point (projectiveSpace k E)),
      p.1 (IsLocalRing.closedPoint k) ∈ Z →
        (A.toMulAction.smul (T.includePoint (c.onPoints t)) p).1 (IsLocalRing.closedPoint k) ∈ Z)
    (hvZ : (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)).1
      (IsLocalRing.closedPoint k) ∈ Z) :
    (projectivePointOfVector
      (b₀.equivFun (topVector b (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M v))
      (b₀.equivFun.map_ne_zero_iff.mpr (topVector_ne_zero b _ M v h))).1
      (IsLocalRing.closedPoint k) ∈ Z := by
  let f := originalTopCurve b₀ b (fun i => characterCocharacterPairing T c (Additive.ofMul (χ i))) M v h
  rw [← originalTopCurve_zero b₀ b _ M v h hM]
  change f.hom ((ProjectivePolynomialCurve.affinePoint 0).1 (IsLocalRing.closedPoint k)) ∈ Z
  apply ProjectivePolynomialCurve.affinePoint_mem_of_nonzero (hZ.preimage f.hom.continuous)
  intro a ha
  change (f (ProjectivePolynomialCurve.affinePoint a)).1 (IsLocalRing.closedPoint k) ∈ Z
  rw [originalTopCurve_nonzero ρ T c A b₀ b χ he hweight M v hv h hM a ha]
  exact hinv _ _ hvZ

end Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
