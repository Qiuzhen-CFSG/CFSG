module

public import Theory.AlgebraicGroup.Bor1.GeneralLinearTangentMatrixUnits
public import Theory.AlgebraicGroup.Bor1.NormalWeights
public import Theory.AlgebraicGroup.Bor1.RepresentationDifferential
public import Theory.AlgebraicGroup.Morphism.CodRestrict

/-!
# General-linear subspace stabilizers and their identity tangents

This module constructs the closed subgroup of the general-linear variety
that stabilizes a prescribed subspace and identifies its identity tangent
with the endomorphisms preserving that subspace. The construction uses the
existing rational-representation stabilizer locus.

For the forward implication, adapted-basis matrix coefficients vanish on the
subgroup and are differentiated after restriction. For the reverse
implication, an adapted basis identifies the subgroup with a block parabolic:
diagonal-torus curves give diagonal matrix units, and conjugation by explicit
stabilizing transvections gives every permitted off-diagonal matrix unit.
Expanding a preserving endomorphism in this matrix-unit basis completes the
proof. Thus the reverse direction is supplied by explicit reduced geometric
curves rather than by differentiating set-theoretic equations through their
radical. This is the standard block-upper-triangular tangent calculation for
the general-linear parabolic stabilizing a subspace.
-/

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup
open scoped BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private noncomputable def generalLinearPointMulEquivOf
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Variety.Point (glVarietyOf k V) ≃*
      LinearMap.GeneralLinearGroup k V := by
  let eGL : GL (Fin (Module.finrank k V)) k ≃*
      LinearMap.GeneralLinearGroup k
        (Fin (Module.finrank k V) → k) :=
    Matrix.GeneralLinearGroup.toLin
  let eLin : LinearMap.GeneralLinearGroup k
      (Fin (Module.finrank k V) → k) ≃*
        LinearMap.GeneralLinearGroup k V :=
    LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun.symm
  exact (translationGLPointMulEquiv (k := k)
    (Module.finrank k V)).trans (eGL.trans eLin)

private noncomputable def generalLinearNaturalRepresentation
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    RationalRepresentation (glVarietyOf k V) V where
  action := (generalLinearPointMulEquivOf b).toMonoidHom

omit [CharZero k] [FiniteDimensional k V] in
private lemma generalLinearNaturalRepresentation_action
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (glVarietyOf k V)) :
    (generalLinearNaturalRepresentation b).action x =
      glPointEquivOf k V b x := rfl

omit [CharZero k] [FiniteDimensional k V] in
private theorem generalLinearNaturalRepresentation_isRational
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    IsRationalRepresentation (generalLinearNaturalRepresentation b) := by
  refine ⟨b, AlgebraicGroup.Morphism.id (glVarietyOf k V), ?_⟩
  intro x
  exact (generalLinearNaturalRepresentation_action b x).symm

omit [IsAlgClosed k] [CharZero k] in
private lemma map_eq_iff_mapsTo_of_generalLinear
    (A : LinearMap.GeneralLinearGroup k V) (W : Submodule k V) :
    Submodule.map (A : Module.End k V) W = W ↔
      ∀ w : V, w ∈ W → (A : Module.End k V) w ∈ W := by
  constructor
  · intro h w hw
    have : (A : Module.End k V) w ∈
        Submodule.map (A : Module.End k V) W := ⟨w, hw, rfl⟩
    rwa [h] at this
  · intro h
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.map_le_iff_le_comap]
      exact h
    · exact LinearEquiv.finrank_map_eq A.toLinearEquiv W

/-- The closed subgroup of the general-linear variety that stabilizes `W`. -/
public noncomputable def generalLinearSubspaceStabilizer
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (W : Submodule k V) : ClosedSubgroup (glVarietyOf k V) := by
  let rho := generalLinearNaturalRepresentation b
  let S : Subgroup (Variety.Point (glVarietyOf k V)) :=
    (subspaceStabilizer k V W).comap rho.action
  apply ClosedSubgroup.ofSubgroup S
  have hcarrier : (S : Set (Variety.Point (glVarietyOf k V))) =
      {x | Submodule.map (rho.action x : Module.End k V) W = W} := by
    ext x
    change (∀ w : V, w ∈ W → (rho.action x : Module.End k V) w ∈ W) ↔ _
    exact (map_eq_iff_mapsTo_of_generalLinear (rho.action x) W).symm
  rw [hcarrier]
  exact Theory.AlgebraicGroup.Bor1.RationalRepresentation.subspaceStabilizer_isZariskiClosed_Bor1 rho
    (generalLinearNaturalRepresentation_isRational b) W

omit [CharZero k] in
/-- Membership in the general-linear subspace stabilizer is equality of the
image subspace with the original subspace. -/
public theorem mem_generalLinearSubspaceStabilizer_iff
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (W : Submodule k V) (x : Variety.Point (glVarietyOf k V)) :
    x ∈ generalLinearSubspaceStabilizer b W ↔
      Submodule.map
        ((glPointEquivOf k V b x : LinearMap.GeneralLinearGroup k V) :
          Module.End k V) W = W := by
  change (∀ w : V, w ∈ W →
      ((generalLinearNaturalRepresentation b).action x : Module.End k V) w ∈ W) ↔ _
  rw [generalLinearNaturalRepresentation_action]
  exact (map_eq_iff_mapsTo_of_generalLinear (glPointEquivOf k V b x) W).symm

private theorem generalLinearNaturalRepresentation_differential
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    rationalRepresentationDifferential
        (generalLinearNaturalRepresentation b) b
        (AlgebraicGroup.Morphism.id (glVarietyOf k V)) =
      generalLinearIdentityTangentLinearMap b := by
  rw [rationalRepresentationDifferential_eq_generalLinear_comp]
  ext D
  simp
  rfl

private theorem identityTangent_generalLinearSubspaceStabilizer_forward
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (W : Submodule k V) (D : IdentityPointDerivation (glVarietyOf k V))
    (hD : D ∈ LinearMap.range (identityTangentMorphismLinearMap
      (generalLinearSubspaceStabilizer b W).inclusion)) :
    ∀ w : V, w ∈ W → generalLinearIdentityTangentLinearMap b D w ∈ W := by
  classical
  obtain ⟨E, rfl⟩ := hD
  obtain ⟨e, hr, hW⟩ := exists_basis_span_initial_Bor1 (k := k) W
  let H := generalLinearSubspaceStabilizer b W
  let rho := generalLinearNaturalRepresentation b
  let f := AlgebraicGroup.Morphism.id (glVarietyOf k V)
  let A : Module.End k V := generalLinearIdentityTangentLinearMap b
    (identityTangentMorphismLinearMap H.inclusion E)
  have hbasis (j : Fin (Module.finrank k W)) :
      A (e (Fin.castLE hr j)) ∈ W := by
    let v := e.equivFun (A (e (Fin.castLE hr j)))
    have hv : ∀ i : Fin (Module.finrank k V),
        Module.finrank k W ≤ i.1 → v i = 0 := by
      intro i hi
      let q := rationalRepresentationLinearMatrixCoefficient rho b f
        (e.dualBasis i) (e (Fin.castLE hr j))
      have hqzero : H.inclusion.toVariety.pullbackAlgHom q = 0 := by
        apply Variety.PolynomialFunction.ext
        intro x
        change q (H.inclusion.onPoints x) = 0
        rw [show q = rationalRepresentationLinearMatrixCoefficient rho b f
            (e.dualBasis i) (e (Fin.castLE hr j)) by rfl,
          rationalRepresentationLinearMatrixCoefficient_apply]
        · have hx : H.inclusion.onPoints x ∈ H := (H.pointEquiv x).property
          have hxmap := (mem_generalLinearSubspaceStabilizer_iff b W
            (H.inclusion.onPoints x)).mp hx
          have hej : e (Fin.castLE hr j) ∈ W := by
            exact hW.ge (Submodule.subset_span ⟨j, rfl⟩)
          have himage :
              ((glPointEquivOf k V b (H.inclusion.onPoints x) :
                LinearMap.GeneralLinearGroup k V) : Module.End k V)
                  (e (Fin.castLE hr j)) ∈ W := by
            have hmem :
                ((glPointEquivOf k V b (H.inclusion.onPoints x) :
                  LinearMap.GeneralLinearGroup k V) : Module.End k V)
                    (e (Fin.castLE hr j)) ∈
                  Submodule.map
                    ((glPointEquivOf k V b (H.inclusion.onPoints x) :
                      LinearMap.GeneralLinearGroup k V) : Module.End k V) W :=
              ⟨e (Fin.castLE hr j), hej, rfl⟩
            rwa [hxmap] at hmem
          have hcoord := (basisSpanCoord V (Module.finrank k V) e
            (Module.finrank k W) hr
            (e.equivFun
              (((glPointEquivOf k V b (H.inclusion.onPoints x) :
                LinearMap.GeneralLinearGroup k V) : Module.End k V)
                  (e (Fin.castLE hr j))))).mp (by simpa [hW] using himage)
          rw [generalLinearNaturalRepresentation_action]
          simpa [Module.Basis.dualBasis_apply] using hcoord i hi
        · intro x
          exact generalLinearNaturalRepresentation_action b x
      rw [show v i = e.dualBasis i (A (e (Fin.castLE hr j))) by simp [v]]
      rw [show A = rationalRepresentationDifferential rho b f
          (identityTangentMorphismLinearMap H.inclusion E) by
        change generalLinearIdentityTangentLinearMap b _ = _
        rw [generalLinearNaturalRepresentation_differential b]]
      rw [rationalRepresentationDifferential_linearMatrixCoefficient]
      change E (H.inclusion.toVariety.pullbackAlgHom q) = 0
      rw [hqzero, map_zero]
    have hspan := (basisSpanCoord V (Module.finrank k V) e
      (Module.finrank k W) hr v).mpr hv
    have hspan' : A (e (Fin.castLE hr j)) ∈
        Submodule.span k (Set.range (fun j : Fin (Module.finrank k W) =>
          e (Fin.castLE hr j))) := by
      simpa [v] using hspan
    rwa [← hW] at hspan'
  intro w hw
  change A w ∈ W
  have hle : Submodule.span k
      (Set.range (fun j : Fin (Module.finrank k W) => e (Fin.castLE hr j))) ≤
        Submodule.comap A W := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact hbasis j
  apply hle
  rwa [← hW]

private noncomputable def basisChangeLinearEquiv
    (b e : Module.Basis (Fin (Module.finrank k V)) k V) : V ≃ₗ[k] V :=
  b.equivFun.trans e.equivFun.symm

omit [IsAlgClosed k] [CharZero k] [FiniteDimensional k V] in
private lemma basisChangeLinearEquiv_apply
    (b e : Module.Basis (Fin (Module.finrank k V)) k V)
    (i : Fin (Module.finrank k V)) :
    basisChangeLinearEquiv b e (b i) = e i := by
  rw [basisChangeLinearEquiv]
  change e.equivFun.symm (b.equivFun (b i)) = e i
  rw [Module.Basis.equivFun_apply, Module.Basis.repr_self,
    Finsupp.single_eq_pi_single, Basis.equivFun_symm_single]

omit [IsAlgClosed k] [CharZero k] [FiniteDimensional k V] in
private lemma basisChangeLinearEquiv_symm_apply
    (b e : Module.Basis (Fin (Module.finrank k V)) k V)
    (i : Fin (Module.finrank k V)) :
    (basisChangeLinearEquiv b e).symm (e i) = b i := by
  apply (basisChangeLinearEquiv b e).injective
  rw [LinearEquiv.apply_symm_apply, basisChangeLinearEquiv_apply]

omit [IsAlgClosed k] [CharZero k] [FiniteDimensional k V] in
private lemma basisChangeLinearEquiv_conj_end
    (b e : Module.Basis (Fin (Module.finrank k V)) k V)
    (p q : Fin (Module.finrank k V)) :
    (basisChangeLinearEquiv b e).conj (b.end (p, q)) = e.end (p, q) := by
  apply e.ext
  intro r
  change basisChangeLinearEquiv b e
      (b.end (p, q) ((basisChangeLinearEquiv b e).symm (e r))) = _
  rw [basisChangeLinearEquiv_symm_apply]
  by_cases hrq : r = q
  · subst r
    simp [Module.Basis.end_apply_apply, basisChangeLinearEquiv_apply]
  · have hqr : q ≠ r := Ne.symm hrq
    simp [Module.Basis.end_apply_apply, hqr]

omit [IsAlgClosed k] [CharZero k] in
private lemma diagonal_generalLinear_preserves_initialSpan
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (r : Nat) (hr : r ≤ Module.finrank k V)
    (A : LinearMap.GeneralLinearGroup k V) (c : Fin (Module.finrank k V) → k)
    (hA : ∀ j, (A : Module.End k V) (e j) = c j • e j) :
    Submodule.map (A : Module.End k V)
        (Submodule.span k (Set.range (fun j : Fin r => e (Fin.castLE hr j)))) =
      Submodule.span k (Set.range (fun j : Fin r => e (Fin.castLE hr j))) := by
  rw [map_eq_iff_mapsTo_of_generalLinear]
  intro w hw
  have hle : Submodule.span k
      (Set.range (fun j : Fin r => e (Fin.castLE hr j))) ≤
        Submodule.comap (A : Module.End k V)
          (Submodule.span k (Set.range (fun j : Fin r => e (Fin.castLE hr j)))) := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨j, rfl⟩
    change (A : Module.End k V) (e (Fin.castLE hr j)) ∈
      Submodule.span k (Set.range (fun j : Fin r => e (Fin.castLE hr j)))
    rw [hA]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact hle hw

omit [IsAlgClosed k] [CharZero k] in
private lemma transvection_generalLinear_preserves_initialSpan
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (r : Nat) (hr : r ≤ Module.finrank k V)
    {p q : Fin (Module.finrank k V)} (hpq : p ≠ q)
    (hallowed : q.val < r → p.val < r) :
    let hcoord : e.coord q (e p) = 0 := by
      simp [Module.Basis.coord_apply, hpq]
    let t : V ≃ₗ[k] V := LinearEquiv.transvection hcoord
    Submodule.map
        ((LinearMap.GeneralLinearGroup.ofLinearEquiv t :
          LinearMap.GeneralLinearGroup k V) : Module.End k V)
        (Submodule.span k (Set.range (fun j : Fin r => e (Fin.castLE hr j)))) =
      Submodule.span k (Set.range (fun j : Fin r => e (Fin.castLE hr j))) := by
  dsimp only
  let hcoord : e.coord q (e p) = 0 := by
    simp [Module.Basis.coord_apply, hpq]
  change Submodule.map
      ((LinearMap.GeneralLinearGroup.ofLinearEquiv
        (LinearEquiv.transvection hcoord) :
          LinearMap.GeneralLinearGroup k V) : Module.End k V)
      (Submodule.span k (Set.range (fun j : Fin r => e (Fin.castLE hr j)))) = _
  rw [map_eq_iff_mapsTo_of_generalLinear]
  intro w hw
  have hle : Submodule.span k
      (Set.range (fun j : Fin r => e (Fin.castLE hr j))) ≤
        Submodule.comap
          ((LinearMap.GeneralLinearGroup.ofLinearEquiv
            (LinearEquiv.transvection hcoord) :
                LinearMap.GeneralLinearGroup k V) : Module.End k V)
          (Submodule.span k (Set.range (fun j : Fin r => e (Fin.castLE hr j)))) := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with ⟨j, rfl⟩
    change LinearEquiv.transvection hcoord (e (Fin.castLE hr j)) ∈
      Submodule.span k (Set.range (fun j : Fin r => e (Fin.castLE hr j)))
    rw [LinearEquiv.transvection.apply]
    apply Submodule.add_mem
    · exact Submodule.subset_span ⟨j, rfl⟩
    · by_cases hqj : q = Fin.castLE hr j
      · have hq : q.val < r := by
          rw [hqj]
          exact j.isLt
        have hp : p.val < r := hallowed hq
        simpa [Module.Basis.coord_apply, hqj] using
          (Submodule.subset_span
            (R := k) ⟨⟨p.val, hp⟩, by simp⟩ : e p ∈
              Submodule.span k
                (Set.range (fun j : Fin r => e (Fin.castLE hr j))))
      · simp [Module.Basis.coord_apply, hqj]
  exact hle hw

omit [IsAlgClosed k] [CharZero k] [FiniteDimensional k V] in
private lemma transvection_conj_diagonal_matrixUnit_adapted
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    {p q : Fin (Module.finrank k V)} (hpq : p ≠ q) :
    let hcoord : e.coord q (e p) = 0 := by
      simp [Module.Basis.coord_apply, hpq]
    let t : V ≃ₗ[k] V := LinearEquiv.transvection hcoord
    t.conj (e.end (q, q)) - e.end (q, q) = e.end (p, q) := by
  dsimp only
  apply e.ext
  intro r
  rw [LinearMap.sub_apply, LinearEquiv.conj_apply]
  change LinearMap.transvection (e.coord q) (e p)
      ((e.end (q, q)) (LinearMap.transvection (e.coord q) (-e p) (e r))) -
        e.end (q, q) (e r) = e.end (p, q) (e r)
  by_cases hrq : r = q
  · subst r
    simp [LinearMap.transvection.apply, Module.Basis.end_apply_apply,
      Ne.symm hpq]
  · simp [LinearMap.transvection.apply, Module.Basis.end_apply_apply,
      Ne.symm hrq]

omit [CharZero k] in
private theorem closedSubgroupTangent_conjugation_mem_range
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) (hg : g ∈ H)
    (D : IdentityPointDerivation G)
    (hD : D ∈ LinearMap.range
      (identityTangentMorphismLinearMap H.inclusion)) :
    identityTangentConjugationLinearMap G g D ∈
      LinearMap.range (identityTangentMorphismLinearMap H.inclusion) := by
  rcases hD with ⟨E, rfl⟩
  let gH : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨g, hg⟩
  let cH : AlgebraicGroup.Morphism H.carrierVariety H.carrierVariety :=
    { toVariety := AlgebraicGroup.conjugationByMorphism H.carrierVariety gH
      map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
      map_mul := by
        intro x y
        simp only [AlgebraicGroup.conjugationByMorphism_apply]
        group }
  refine ⟨identityTangentMorphismLinearMap cH E, ?_⟩
  have hgH : H.inclusion.onPoints gH = g := by
    change (H.pointEquiv (H.pointEquiv.symm ⟨g, hg⟩)).val = g
    rw [H.pointEquiv.apply_symm_apply]
  have hnat := LinearMap.congr_fun
    (identityTangentMorphismLinearMap_conjugation_naturality H.inclusion gH) E
  change identityTangentMorphismLinearMap H.inclusion
      (identityTangentMorphismLinearMap cH E) = _
  change identityTangentMorphismLinearMap H.inclusion
      (identityTangentConjugationLinearMap H.carrierVariety gH E) = _
  simpa [hgH] using hnat

private theorem diagonal_matrixUnit_mem_stabilizer_tangent_range
    (b e : Module.Basis (Fin (Module.finrank k V)) k V)
    (W : Submodule k V) (r : Nat) (hr : r ≤ Module.finrank k V)
    (hW : W = Submodule.span k
      (Set.range (fun j : Fin r => e (Fin.castLE hr j))))
    (q : Fin (Module.finrank k V)) :
    ∃ D : IdentityPointDerivation (glVarietyOf k V),
      D ∈ LinearMap.range (identityTangentMorphismLinearMap
        (generalLinearSubspaceStabilizer b W).inclusion) ∧
      generalLinearIdentityTangentLinearMap b D = e.end (q, q) := by
  classical
  obtain ⟨f, D0, hf, hD0⟩ :=
    exists_basisDiagonalMorphism_identityTangent_matrixUnit b q
  let c : V ≃ₗ[k] V := basisChangeLinearEquiv b e
  let cg : LinearMap.GeneralLinearGroup k V :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv c
  let g : Variety.Point (glVarietyOf k V) :=
    generalLinearRepresentationPoint b cg
  let cAmb : AlgebraicGroup.Morphism (glVarietyOf k V) (glVarietyOf k V) :=
    { toVariety := AlgebraicGroup.conjugationByMorphism (glVarietyOf k V) g
      map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
      map_mul := by
        intro x y
        simp only [AlgebraicGroup.conjugationByMorphism_apply]
        group }
  let cf := cAmb.comp f
  have hcf_action (x : Variety.Point (dVariety k (Module.finrank k V)))
      (j : Fin (Module.finrank k V)) :
      ((glPointEquivOf k V b (cf.onPoints x) :
        LinearMap.GeneralLinearGroup k V) : Module.End k V) (e j) =
          dPointEntry (Module.finrank k V) x j • e j := by
    have hpoint : cf.onPoints x = g * f.onPoints x * g⁻¹ := by
      change cAmb.onPoints (f.onPoints x) = _
      exact AlgebraicGroup.conjugationByMorphism_apply _ _ _
    change ((generalLinearPointMulEquivOf b (cf.onPoints x) :
      LinearMap.GeneralLinearGroup k V) : Module.End k V) (e j) = _
    rw [hpoint, map_mul, map_mul, map_inv]
    have hg : generalLinearPointMulEquivOf b g = cg := by
      change glPointEquivOf k V b g = cg
      exact glPointEquivOf_generalLinearRepresentationPoint b cg
    rw [hg]
    change c
      (((generalLinearPointMulEquivOf b (f.onPoints x) :
        LinearMap.GeneralLinearGroup k V) : Module.End k V)
          (c.symm (e j))) = _
    rw [show c.symm (e j) = b j from basisChangeLinearEquiv_symm_apply b e j]
    change c
      (((glPointEquivOf k V b (f.onPoints x) :
        LinearMap.GeneralLinearGroup k V) : Module.End k V) (b j)) = _
    rw [hf, map_smul, basisChangeLinearEquiv_apply]
  have hcf_mem (x : Variety.Point (dVariety k (Module.finrank k V))) :
      cf.onPoints x ∈ generalLinearSubspaceStabilizer b W := by
    rw [mem_generalLinearSubspaceStabilizer_iff]
    calc
      Submodule.map
          ((glPointEquivOf k V b (cf.onPoints x) :
            LinearMap.GeneralLinearGroup k V) : Module.End k V) W =
          Submodule.map
            ((glPointEquivOf k V b (cf.onPoints x) :
              LinearMap.GeneralLinearGroup k V) : Module.End k V)
            (Submodule.span k
              (Set.range (fun j : Fin r => e (Fin.castLE hr j)))) := by rw [← hW]
      _ = Submodule.span k
            (Set.range (fun j : Fin r => e (Fin.castLE hr j))) :=
        diagonal_generalLinear_preserves_initialSpan e r hr _ _ (hcf_action x)
      _ = W := hW.symm
  let H := generalLinearSubspaceStabilizer b W
  let fH : AlgebraicGroup.Morphism
      (dVariety k (Module.finrank k V)) H.carrierVariety :=
    cf.codRestrictClosedSubgroup H hcf_mem
  let E := identityTangentMorphismLinearMap fH D0
  let D := identityTangentMorphismLinearMap H.inclusion E
  refine ⟨D, ⟨E, rfl⟩, ?_⟩
  have hcomp : H.inclusion.comp fH = cf := by
    apply AlgebraicGroup.Morphism.ext
    funext j
    exact cf.codRestrictClosedSubgroup_inclusion_apply H hcf_mem j
  have hD : D = identityTangentConjugationLinearMap
      (glVarietyOf k V) g (identityTangentMorphismLinearMap f D0) := by
    change identityTangentMorphismLinearMap H.inclusion
      (identityTangentMorphismLinearMap fH D0) = _
    calc
      identityTangentMorphismLinearMap H.inclusion
          (identityTangentMorphismLinearMap fH D0) =
          identityTangentMorphismLinearMap (H.inclusion.comp fH) D0 := by
            rw [identityTangentMorphismLinearMap_comp]
            rfl
      _ = identityTangentMorphismLinearMap cf D0 := by rw [hcomp]
      _ = identityTangentMorphismLinearMap (cAmb.comp f) D0 := rfl
      _ = identityTangentMorphismLinearMap cAmb
          (identityTangentMorphismLinearMap f D0) := by
            rw [identityTangentMorphismLinearMap_comp]
            rfl
      _ = identityTangentConjugationLinearMap
          (glVarietyOf k V) g (identityTangentMorphismLinearMap f D0) := rfl
  rw [hD, generalLinearIdentityTangentLinearMap_conjugation_eq, hD0,
    generalLinearConjugationRepresentation_apply,
    glPointEquivOf_generalLinearRepresentationPoint]
  exact basisChangeLinearEquiv_conj_end b e q q

private theorem matrixUnit_mem_stabilizer_tangent_range
    (b e : Module.Basis (Fin (Module.finrank k V)) k V)
    (W : Submodule k V) (r : Nat) (hr : r ≤ Module.finrank k V)
    (hW : W = Submodule.span k
      (Set.range (fun j : Fin r => e (Fin.castLE hr j))))
    (p q : Fin (Module.finrank k V))
    (hallowed : q.val < r → p.val < r) :
    ∃ D : IdentityPointDerivation (glVarietyOf k V),
      D ∈ LinearMap.range (identityTangentMorphismLinearMap
        (generalLinearSubspaceStabilizer b W).inclusion) ∧
      generalLinearIdentityTangentLinearMap b D = e.end (p, q) := by
  classical
  obtain ⟨Dq, hDqmem, hDq⟩ :=
    diagonal_matrixUnit_mem_stabilizer_tangent_range b e W r hr hW q
  by_cases hpq : p = q
  · subst p
    exact ⟨Dq, hDqmem, hDq⟩
  · let hcoord : e.coord q (e p) = 0 := by
      simp [Module.Basis.coord_apply, hpq]
    let t : V ≃ₗ[k] V := LinearEquiv.transvection hcoord
    let tg : LinearMap.GeneralLinearGroup k V :=
      LinearMap.GeneralLinearGroup.ofLinearEquiv t
    let g : Variety.Point (glVarietyOf k V) :=
      generalLinearRepresentationPoint b tg
    have hg : glPointEquivOf k V b g = tg :=
      glPointEquivOf_generalLinearRepresentationPoint b tg
    have hgmem : g ∈ generalLinearSubspaceStabilizer b W := by
      rw [mem_generalLinearSubspaceStabilizer_iff, hg]
      calc
        Submodule.map (tg : Module.End k V) W =
            Submodule.map (tg : Module.End k V)
              (Submodule.span k
                (Set.range (fun j : Fin r => e (Fin.castLE hr j)))) := by rw [← hW]
        _ = Submodule.span k
              (Set.range (fun j : Fin r => e (Fin.castLE hr j))) :=
          transvection_generalLinear_preserves_initialSpan e r hr hpq hallowed
        _ = W := hW.symm
    let Dg := identityTangentConjugationLinearMap (glVarietyOf k V) g Dq
    have hDgmem : Dg ∈ LinearMap.range (identityTangentMorphismLinearMap
        (generalLinearSubspaceStabilizer b W).inclusion) :=
      closedSubgroupTangent_conjugation_mem_range
        (generalLinearSubspaceStabilizer b W) g hgmem Dq hDqmem
    refine ⟨Dg - Dq, Submodule.sub_mem _ hDgmem hDqmem, ?_⟩
    change generalLinearIdentityTangentLinearMap b
      (identityTangentConjugationLinearMap (glVarietyOf k V) g Dq - Dq) = _
    rw [map_sub, generalLinearIdentityTangentLinearMap_conjugation_eq, hDq,
      generalLinearConjugationRepresentation_apply, hg]
    change t.conj (e.end (q, q)) - e.end (q, q) = e.end (p, q)
    exact transvection_conj_diagonal_matrixUnit_adapted e hpq

omit [IsAlgClosed k] [CharZero k] [FiniteDimensional k V] in
private lemma basisEnd_coord_eq_coord_apply
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (A : Module.End k V) (p q : Fin (Module.finrank k V)) :
    e.end.coord (p, q) A = e.coord p (A (e q)) := by
  rw [Module.Basis.coord_apply, Module.Basis.end_repr_apply]
  simp [Matrix.stdBasis, LinearMap.toMatrix_apply]

private theorem identityTangent_generalLinearSubspaceStabilizer_reverse
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (W : Submodule k V) (D : IdentityPointDerivation (glVarietyOf k V))
    (hD : ∀ w : V, w ∈ W →
      generalLinearIdentityTangentLinearMap b D w ∈ W) :
    D ∈ LinearMap.range (identityTangentMorphismLinearMap
      (generalLinearSubspaceStabilizer b W).inclusion) := by
  classical
  obtain ⟨e, hr, hW⟩ := exists_basis_span_initial_Bor1 (k := k) W
  let r := Module.finrank k W
  change r ≤ Module.finrank k V at hr
  change W = Submodule.span k
    (Set.range (fun j : Fin r => e (Fin.castLE hr j))) at hW
  let A : Module.End k V := generalLinearIdentityTangentLinearMap b D
  let R : Submodule k (IdentityPointDerivation (glVarietyOf k V)) :=
    LinearMap.range (identityTangentMorphismLinearMap
      (generalLinearSubspaceStabilizer b W).inclusion)
  let T : Submodule k (Module.End k V) :=
    R.map (generalLinearIdentityTangentLinearMap b)
  have hzero (p q : Fin (Module.finrank k V))
      (hp : r ≤ p.val) (hq : q.val < r) :
      e.end.coord (p, q) A = 0 := by
    rw [basisEnd_coord_eq_coord_apply]
    have heq : e q ∈ W := by
      apply hW.ge
      exact Submodule.subset_span
        ⟨⟨q.val, hq⟩, by simp⟩
    have hAe : A (e q) ∈ W := hD (e q) heq
    have hspan : A (e q) ∈ Submodule.span k
        (Set.range (fun j : Fin r => e (Fin.castLE hr j))) := by
      rwa [← hW]
    have hc := (basisSpanCoord V (Module.finrank k V) e r hr
      (e.equivFun (A (e q)))).mp (by simpa using hspan)
    simpa [Module.Basis.dualBasis_apply] using hc p hp
  have hunit (p q : Fin (Module.finrank k V))
      (hallowed : q.val < r → p.val < r) : e.end (p, q) ∈ T := by
    obtain ⟨Dpq, hDpq, hmap⟩ :=
      matrixUnit_mem_stabilizer_tangent_range b e W r hr hW p q hallowed
    exact Submodule.mem_map.mpr ⟨Dpq, hDpq, hmap⟩
  have hAT : A ∈ T := by
    rw [← e.end.sum_repr A]
    apply Submodule.sum_mem
    intro pq _
    rcases pq with ⟨p, q⟩
    by_cases hallowed : q.val < r → p.val < r
    · exact Submodule.smul_mem T _ (hunit p q hallowed)
    · simp only [Classical.not_imp, not_lt] at hallowed
      rcases hallowed with ⟨hq, hp⟩
      change e.end.coord (p, q) A • e.end (p, q) ∈ T
      rw [hzero p q hp hq, zero_smul]
      exact Submodule.zero_mem T
  rcases Submodule.mem_map.mp hAT with ⟨D', hD'mem, hD'eq⟩
  have hD'eqD : D' = D := by
    apply generalLinearIdentityTangentLinearMap_injective b
    simpa [A] using hD'eq
  rwa [hD'eqD] at hD'mem

/-- The identity tangent of the general-linear subspace stabilizer consists
exactly of the endomorphisms preserving the stabilized subspace. -/
public theorem identityTangent_generalLinearSubspaceStabilizer_range_iff
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (W : Submodule k V) (D : IdentityPointDerivation (glVarietyOf k V)) :
    D ∈ LinearMap.range (identityTangentMorphismLinearMap
        (generalLinearSubspaceStabilizer b W).inclusion) ↔
      ∀ w : V, w ∈ W → generalLinearIdentityTangentLinearMap b D w ∈ W := by
  constructor
  · exact identityTangent_generalLinearSubspaceStabilizer_forward b W D
  · exact identityTangent_generalLinearSubspaceStabilizer_reverse b W D

end Theory.AlgebraicGroup.Bor1
