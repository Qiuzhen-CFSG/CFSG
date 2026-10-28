module

public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.AffineGeometry
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.InvariantHyperplane
public import Theory.AlgebraicGroup.Variety.ProjectiveLinearAction
public import Theory.AlgebraicGroup.Bor1.SolvableCompleteFixedPoint
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.ClosedOrbit
public import Theory.AlgebraicGroup.Tori.Power
public import Theory.AlgebraicGroup.Variety.MorphicActionPullback

/-!
# A torus fixed point outside a prescribed projective image

A dual torus weight gives an invariant hyperplane avoiding the chosen point.
Its complement is the actual affine basic open of the homogeneous linear
polynomial. A nonconstant complete connected image meets the hyperplane, so
the solvable fixed-point theorem applies to its invariant complete preimage.
This proves the fixed-point escape used in Borel, §§13.5–13.6, without a
finite fixed-point or dimension certificate.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped BigOperators LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]

noncomputable def dualHomogeneousPolynomial
    (b : Module.Basis (Fin (Module.finrank k E)) k E) (l : Module.Dual k E) :
    MvPolynomial (Fin (Module.finrank k E)) k :=
  ∑ i, MvPolynomial.C (l (b i)) * MvPolynomial.X i

omit [IsAlgClosed k] [FiniteDimensional k E] in
theorem dualHomogeneousPolynomial_degree
    (b : Module.Basis (Fin (Module.finrank k E)) k E) (l : Module.Dual k E) :
    dualHomogeneousPolynomial b l ∈ projectiveGrading k (Fin (Module.finrank k E)) 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact MvPolynomial.isHomogeneous_C_mul_X (l (b j)) j

omit [IsAlgClosed k] [FiniteDimensional k E] in
theorem dualHomogeneousPolynomial_eval
    (b : Module.Basis (Fin (Module.finrank k E)) k E) (l : Module.Dual k E) (v : E) :
    MvPolynomial.eval₂Hom (RingHom.id k) (b.equivFun v)
      (dualHomogeneousPolynomial b l) = l v := by
  simp only [dualHomogeneousPolynomial, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    RingHom.id_apply, MvPolynomial.eval₂Hom_X']
  calc
    _ = l (∑ i, b.equivFun v i • b i) := by
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
    _ = l v := congrArg l (b.sum_repr v)

noncomputable def projectiveHyperplaneOpen
    (b : Module.Basis (Fin (Module.finrank k E)) k E) (l : Module.Dual k E) :
    (projectiveSpace k E).toScheme.Opens :=
  Proj.basicOpen (projectiveGrading k (Fin (Module.finrank k E)))
    (dualHomogeneousPolynomial b l)

omit [IsAlgClosed k] in
/-- The hyperplane complement is the literal projective basic open. -/
theorem projectiveHyperplaneOpen_eq
    (b : Module.Basis (Fin (Module.finrank k E)) k E) (l : Module.Dual k E) :
    projectiveHyperplaneOpen b l =
      Proj.basicOpen (projectiveGrading k (Fin (Module.finrank k E)))
        (dualHomogeneousPolynomial b l) := by rfl

instance projectiveHyperplaneOpen_isAffine
    (b : Module.Basis (Fin (Module.finrank k E)) k E) (l : Module.Dual k E) :
    IsAffine (projectiveHyperplaneOpen b l).toScheme :=
  (IsAffine.iff_of_isIso (Proj.basicOpenIsoSpec
    (projectiveGrading k (Fin (Module.finrank k E)))
    (dualHomogeneousPolynomial b l) (dualHomogeneousPolynomial_degree b l)
    Nat.zero_lt_one).hom).mpr inferInstance

omit [IsAlgClosed k] in
theorem projectiveHyperplaneOpen_vector_mem_iff
    (b : Module.Basis (Fin (Module.finrank k E)) k E) (l : Module.Dual k E)
    (v : E) (hv : v ≠ 0) :
    (projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv)).1
      (IsLocalRing.closedPoint k) ∈ projectiveHyperplaneOpen b l ↔ l v ≠ 0 := by
  change dualHomogeneousPolynomial b l ∉
    ((projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv)).1
      (IsLocalRing.closedPoint k)).asHomogeneousIdeal ↔ l v ≠ 0
  exact not_congr ((projectivePointOfVector_mem_iff (b.equivFun v)
    (b.equivFun.map_ne_zero_iff.mpr hv) (dualHomogeneousPolynomial_degree b l)).trans
    (by rw [dualHomogeneousPolynomial_eval]))


theorem exists_projective_vector
    (b : Module.Basis (Fin (Module.finrank k E)) k E) (p : Point (projectiveSpace k E)) :
    ∃ (v : E) (hv : v ≠ 0),
      p = projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv) := by
  let q := projectiveSpacePointEquivOf b p
  refine ⟨q.rep, q.rep_nonzero, ?_⟩
  apply (projectiveSpacePointEquivOf b).injective
  rw [projectiveSpacePointEquivOf_projectivePointOfVector]
  exact (Projectivization.mk_rep q).symm

theorem projectiveHyperplaneOpen_not_mem_of_map
    (b : Module.Basis (Fin (Module.finrank k E)) k E) (l : Module.Dual k E)
    (a : LinearMap.GeneralLinearGroup k E)
    (hl : ∀ v, l v = 0 → l (a.1 v) = 0)
    (p q : Point (projectiveSpace k E))
    (he : projectiveSpacePointEquivOf b q =
      Projectivization.map a.1 a.toLinearEquiv.injective (projectiveSpacePointEquivOf b p))
    (hp : p.1 (IsLocalRing.closedPoint k) ∉ projectiveHyperplaneOpen b l) :
    q.1 (IsLocalRing.closedPoint k) ∉ projectiveHyperplaneOpen b l := by
  obtain ⟨v, hv, rfl⟩ := exists_projective_vector b p
  have hav : a.1 v ≠ 0 := a.toLinearEquiv.map_ne_zero_iff.mpr hv
  have hq : q = projectivePointOfVector (b.equivFun (a.1 v))
      (b.equivFun.map_ne_zero_iff.mpr hav) := by
    apply (projectiveSpacePointEquivOf b).injective
    rw [he, projectiveSpacePointEquivOf_projectivePointOfVector b v hv,
      projectiveSpacePointEquivOf_projectivePointOfVector b (a.1 v) hav]
    rfl
  have hlv : l v = 0 := by
    by_contra h
    exact hp ((projectiveHyperplaneOpen_vector_mem_iff b l v hv).mpr h)
  rw [hq]
  intro h
  exact ((projectiveHyperplaneOpen_vector_mem_iff b l (a.1 v) hav).mp h) (hl v hlv)

variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
variable {X : Geometric k}

/-- A nonconstant complete connected projective image has a torus fixed point
whose image differs from any prescribed point. -/
theorem MorphicAction.exists_torus_fixedPoint_separating
    (A : MorphicAction G X) (hX : IsComplete X) (hconn : IsConnected X)
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (T : ClosedSubgroup G) (hT : IsTorus T.carrierVariety)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (f : Morphism X (projectiveSpace k E))
    (he : ∀ (t : Variety.Point T.carrierVariety) (x : Point X),
      projectiveSpacePointEquivOf b (f (A.toMulAction.smul (T.includePoint t) x)) =
      Projectivization.map (ρ.action (T.includePoint t)).1
        (ρ.action (T.includePoint t)).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b (f x)))
    (x z : Point X) (hxz : f x ≠ f z) :
    ∃ y : Point X,
      (∀ t : Variety.Point T.carrierVariety, A.toMulAction.smul (T.includePoint t) y = y) ∧
      f y ≠ f x := by
  obtain ⟨v, hv, hfx⟩ := exists_projective_vector b (f x)
  obtain ⟨l, hlv, hlinv⟩ := exists_invariant_dual_nonzero ρ hρ T hT v hv
  let U := projectiveHyperplaneOpen b l
  have hxU : (f x).1 (IsLocalRing.closedPoint k) ∈ U := by
    rw [hfx]
    exact (projectiveHyperplaneOpen_vector_mem_iff b l v hv).mpr hlv
  obtain ⟨w, hw⟩ := f.exists_point_outside_affine_open hconn hX U x z hxz
  let Z : Closeds X.toScheme :=
    ⟨(f.hom ⁻¹' (U : Set (projectiveSpace k E).toScheme))ᶜ,
      (U.isOpen.preimage f.hom.continuous).isClosed_compl⟩
  let C := reducedClosedSubvariety X Z
  let AT := A.pullbackGroup T.inclusion
  have hinv : ∀ (t : Variety.Point T.carrierVariety) (p : Point X),
      p.1 (IsLocalRing.closedPoint k) ∈ Z →
      (AT.toMulAction.smul t p).1 (IsLocalRing.closedPoint k) ∈ Z := by
    intro t p hp
    exact projectiveHyperplaneOpen_not_mem_of_map b l (ρ.action (T.includePoint t))
      (hlinv t) (f p) (f (A.toMulAction.smul (T.includePoint t) p)) (he t p) hp
  obtain ⟨w', hw', _⟩ := (point_mem_reducedClosedSubvariety_iff X Z w).mp hw
  have hne : Nonempty (Point C.toGeometric) := ⟨w'⟩
  have hsol : Group.IsSolvable (Variety.Point T.carrierVariety) :=
    Group.isSolvable_of_comm (isMulCommutative_iff.mp hT.isMulCommutative)
  obtain ⟨y, hy⟩ := MorphicAction.exists_fixedPoint_of_isConnected_isSolvable_isComplete
    (AT.onInvariantReducedClosedSubvariety Z hinv) hT.isConnected hsol
      (reducedClosedSubvariety_isComplete Z hX) hne
  refine ⟨C.inclusion y, ?_, ?_⟩
  · intro t
    have hh := AT.onInvariantReducedClosedSubvariety_inclusion Z hinv t y
    rw [hy] at hh
    exact hh.symm
  · have hyZ : (C.inclusion y).1 (IsLocalRing.closedPoint k) ∈ Z := by
      rw [point_mem_reducedClosedSubvariety_iff]
      refine ⟨y, rfl, ?_⟩
      intro y' heq
      apply Subtype.ext
      exact (cancel_mono C.inclusion.hom).mp (congrArg Subtype.val heq)
    change (f (C.inclusion y)).1 (IsLocalRing.closedPoint k) ∉ U at hyZ
    intro hfy
    rw [hfy] at hyZ
    exact hyZ hxU

end Theory.AlgebraicGroup.Variety.Geometric
