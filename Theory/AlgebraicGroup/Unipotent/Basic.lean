module

public import Theory.AlgebraicGroup.ClosedSubgroup.Centralizer
public import Theory.AlgebraicGroup.ClosedSubgroup.FiniteIndex
public import Theory.AlgebraicGroup.Representations.Unipotent.Algebraic
public import Theory.AlgebraicGroup.Representations.Unipotent.Solvable
public import Theory.AlgebraicGroup.Solvable.Triangular

universe u

set_option linter.style.haveILetI false

/-! Basic permanence and group-theoretic properties of unipotent algebraic
groups from GLS §1.3. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A closed subgroup realizes the unipotent radical when its points are
exactly the unipotent elements of the ambient group. -/
@[expose]
public def IsUnipotentRadicalSubgroup
    {G : Variety k} [AlgebraicGroup G] (U : ClosedSubgroup G) : Prop :=
  ∀ x : Variety.Point G, x ∈ U ↔ IsUnipotentElement G x

/-- A closed subgroup containing exactly the ambient unipotent elements
contains every closed unipotent subgroup. -/
public lemma IsUnipotentRadicalSubgroup.maximal
    {G : Variety k} [AlgebraicGroup G]
    {U : ClosedSubgroup G} (hU : IsUnipotentRadicalSubgroup U)
    (N : ClosedSubgroup G)
    (hN : IsUnipotentAlgebraicGroup N.carrierVariety) :
    N ≤ U := by
  rw [ClosedSubgroup.le_iff_le_toSubgroup]
  intro x hx
  have hNpoint : IsUnipotentElement N.carrierVariety
      (N.pointEquiv.symm ⟨x, hx⟩) := hN _
  have hxUnipotent : IsUnipotentElement G x :=
    (closedSubgroup_unipotentElement_iff N hx).mpr hNpoint
  exact (hU x).2 hxUnipotent

/-- A pointwise-unipotent algebraic group in characteristic zero is
connected. -/
public theorem IsUnipotentAlgebraicGroup.isConnected_of_ringChar_zero
    (G : Variety k) [AlgebraicGroup G]
    (hG : IsUnipotentAlgebraicGroup G) (hchar : ringChar k = 0) :
    Variety.IsConnected G := by
  let G0 := AlgebraicGroup.identityComponentClosedSubgroup G
  let : G0.toSubgroup.Normal := by
    simpa [G0, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      AlgebraicGroup.identityComponentClosedSubgroup_isNormal G
  let : G0.toSubgroup.FiniteIndex := by
    simpa [G0, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      AlgebraicGroup.identityComponentSubgroup_finiteIndex G
  obtain ⟨Q, hQgroup, π, hQfinite, _, hπker⟩ :=
    G0.finiteQuotientProjection_exists
  letI : AlgebraicGroup Q := hQgroup
  let : Finite (Variety.Point Q) := hQfinite
  have hcomponent : AlgebraicGroup.identityComponent G = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    intro x _
    have hπunipotent : IsUnipotentElement Q (π.onPoints x) :=
      morphism_preserves_unipotentElement π x (hG x)
    let n := orderOf (π.onPoints x)
    have hn : 0 < n := orderOf_pos (π.onPoints x)
    have hπsemisimple : IsSemisimpleElement Q (π.onPoints x) := by
      apply finiteOrder_coprimeChar_implies_semisimple (π.onPoints x) n hn
      · rw [hchar]
        exact fun h => (Nat.ne_of_gt hn) (Nat.eq_zero_of_zero_dvd h)
      · exact pow_orderOf_eq_one _
    have hπone : π.onPoints x = 1 :=
      semisimple_unipotent_eq_one (π.onPoints x) hπsemisimple hπunipotent
    have hxker : x ∈ π.kernel := MonoidHom.mem_ker.mpr hπone
    rw [hπker] at hxker
    change x ∈ AlgebraicGroup.identityComponentSubgroup G
    simpa [G0, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      hxker
  exact (identityComponent_eq_univ_iff_isConnected G).mp hcomponent

/-- Closed algebraic subgroups of unipotent algebraic groups are unipotent. -/
public theorem IsUnipotentAlgebraicGroup.closedSubgroup
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsUnipotentAlgebraicGroup G) (H : ClosedSubgroup G) :
    IsUnipotentAlgebraicGroup H.carrierVariety := by
  intro x
  simpa using closedSubgroup_unipotent_of_ambient H
    (H.pointEquiv x).property (hG (H.pointEquiv x).1)

/-- Surjective algebraic-group images of unipotent groups are unipotent. -/
public theorem IsUnipotentAlgebraicGroup.of_surjective
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (hG : IsUnipotentAlgebraicGroup G) (φ : AlgebraicGroup.Morphism G H)
    (hφ : Function.Surjective φ.onPoints) :
    IsUnipotentAlgebraicGroup H := by
  intro y
  obtain ⟨x, rfl⟩ := hφ y
  exact morphism_preserves_unipotentElement φ x (hG x)

/-- The rational-point group of a unipotent algebraic group is solvable. -/
public theorem isSolvable_of_isUnipotentAlgebraicGroup
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsUnipotentAlgebraicGroup G) :
    Group.IsSolvable (Variety.Point G) := by
  let : Module.Finite k (coordinateTranslationSubmodule G) :=
    coordinateTranslationSubmodule_finite G
  apply isSolvable_of_injective_unipotent_generalLinearRepresentation
    (coordinateTranslationRepresentation G)
    (coordinateTranslationRepresentation_injective G)
  intro g
  exact ⟨Module.finrank k (coordinateTranslationSubmodule G),
    coordinateTranslationRepresentation_sub_one_pow_finrank_eq_zero hG g⟩

/-- A unipotent algebraic group has a nilpotent rational-point group. -/
public theorem unipotentGroup_isNilpotent
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsUnipotentAlgebraicGroup G) :
    Group.IsNilpotent (Variety.Point G) := by
  let : Module.Finite k (coordinateTranslationSubmodule G) :=
    coordinateTranslationSubmodule_finite G
  let ρ := coordinateTranslationRepresentation G
  have hunipotent : ∀ g : Variety.Point G,
      IsNilpotent (((ρ g : LinearMap.GeneralLinearGroup k
        (coordinateTranslationSubmodule G)) :
          Module.End k (coordinateTranslationSubmodule G)) - 1) := by
    intro g
    exact ⟨Module.finrank k (coordinateTranslationSubmodule G),
      coordinateTranslationRepresentation_sub_one_pow_finrank_eq_zero hG g⟩
  obtain ⟨b, F, hb, hstable, _, _⟩ :=
    Subrepresentation.exists_adapted_basis_uUnipotentGL_hom_of_pointwise_unipotent
      ρ hunipotent
  obtain ⟨φ, _, hφ⟩ :=
    Subrepresentation.representation_to_uUnipotentGL_hom_injective_of_injective
      ρ b F hstable hb hunipotent (coordinateTranslationRepresentation_injective G)
  exact isNilpotent_of_injective φ hφ (uUnipotentGL_isNilpotent _)

/-- Every positive-dimensional unipotent algebraic group has
positive-dimensional center. -/
public theorem unipotent_positiveCenter_dimension
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsUnipotentAlgebraicGroup G)
    (hpositive : 0 < Variety.dimension G) :
    0 < Variety.dimension
      (ClosedSubgroup.centralizer
        (ClosedSubgroup.top (G := G))).carrierVariety :=
  positive_dimension_centralizer_of_nilpotent
    (unipotentGroup_isNilpotent hG) hpositive

/-- An algebraic group is unipotent when it is algebraically isomorphic to a
closed subgroup of an upper-unitriangular group. -/
public theorem unipotent_of_upperUnitriangularIso
    {G : Variety k} [AlgebraicGroup G]
    (hG : ∃ n : ℕ, ∃ H : ClosedSubgroup (uVariety k n),
      letI := H.carrierAlgebraicGroup
      Nonempty (AlgebraicGroup.Iso G H.carrierVariety)) :
    IsUnipotentAlgebraicGroup G := by
  obtain ⟨n, H, hG⟩ := hG
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  obtain ⟨e⟩ := hG
  have hH : IsUnipotentAlgebraicGroup H.carrierVariety :=
    (uVariety_isUnipotentAlgebraicGroup_characteristicFree
      (k := k) n).closedSubgroup H
  exact hH.of_surjective e.inv fun x ↦
    ⟨e.hom.onPoints x, e.hom_inv_id x⟩

/-- A unipotent algebraic group is algebraically isomorphic to a closed
subgroup of an upper-unitriangular group. -/
public theorem upperUnitriangularIso_of_unipotent
    {G : Variety k} [AlgebraicGroup G]
    (hG : IsUnipotentAlgebraicGroup G) :
    ∃ n : ℕ, ∃ H : ClosedSubgroup (uVariety k n),
      letI := H.carrierAlgebraicGroup
      Nonempty (AlgebraicGroup.Iso G H.carrierVariety) := by
  let V := coordinateTranslationSubmodule G
  let : Module.Finite k V := coordinateTranslationSubmodule_finite G
  let ρ : RationalRepresentation G V :=
    coordinateTranslationRationalRepresentation G
  have hρ : IsRationalRepresentation ρ :=
    coordinateTranslationRationalRepresentation_isRational G
  have hunipotent : ∀ g : Variety.Point G,
      IsNilpotent ((ρ.action g : Module.End k V) - 1) := by
    intro g
    exact ⟨Module.finrank k V,
      coordinateTranslationRepresentation_sub_one_pow_finrank_eq_zero hG g⟩
  obtain ⟨b, F, hb, hstable, _, _⟩ :=
    Subrepresentation.exists_adapted_basis_uUnipotentGL_hom_of_pointwise_unipotent
      ρ.action hunipotent
  let ρlinear : Representation k (Variety.Point G) V :=
    { toFun := fun g ↦ (ρ.action g : Module.End k V)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp }
  have hunitriangular : ∀ g, uUnipotent (Module.finrank k V)
      (LinearMap.toMatrix b b (ρ.action g : Module.End k V)) := by
    intro g
    exact Subrepresentation.representation_toMatrix_basis_is_uUnipotent_of_pointwise_unipotent
      ρlinear b F hstable hb hunipotent g
  let f := Subrepresentation.unitriangularRepresentationMorphismOfBasis
    ρ hρ b hunitriangular
  have hinjective : Function.Injective f.onPoints :=
    Subrepresentation.unitriangularRepresentationMorphismOfBasis_injective
      ρ hρ b hunitriangular (coordinateTranslationRepresentation_injective G)
  have hcoordinate : ∀ c : G.Coordinates,
      ∃ q : Variety.PolynomialFunction (uVariety k (Module.finrank k V)),
        Variety.PolynomialFunction.pullback f.toVariety q =
          Variety.PolynomialFunction.ofPolynomial G (MvPolynomial.X c) := by
    intro c
    let K : Module.Dual k V :=
      polynomialFunctionSubspaceEvaluation G V 1
    let v : V := coordinateTranslationCoordinateVector G c
    let qT : Variety.PolynomialFunction (tVariety k (Module.finrank k V)) :=
      triangularLinearMatrixCoefficientPreimage (k := k) b K v
    let qU : Variety.PolynomialFunction (uVariety k (Module.finrank k V)) :=
      Variety.PolynomialFunction.pullback
        (uToTMorphism (k := k) (Module.finrank k V)).toVariety qT
    refine ⟨qU, ?_⟩
    apply Variety.PolynomialFunction.ext
    intro g
    change qT ((uToTMorphism (k := k) (Module.finrank k V)).onPoints
        (f.onPoints g)) = coordinatePolynomialFunction G c g
    rw [Subrepresentation.uToTMorphism_unitriangularRepresentationMorphismOfBasis
      ρ hρ b hunitriangular]
    rw [triangularLinearMatrixCoefficientPreimage_apply ρ hρ b
      (fun x ↦ (hunitriangular x).1) K v g]
    change (rightTranslationOnCoordinateSubmodule G g v).val 1 =
      coordinatePolynomialFunction G c g
    rw [rightTranslationOnCoordinateSubmodule_apply,
      rightTranslationPullback_apply]
    change coordinatePolynomialFunction G c (1 * g) =
      coordinatePolynomialFunction G c g
    rw [one_mul]
  letI : AlgebraicGroup f.imageClosedSubgroup.carrierVariety :=
    f.imageClosedSubgroup.carrierAlgebraicGroup
  obtain ⟨e, _⟩ :=
    f.iso_imageClosedSubgroup_of_coordinate_preimage hinjective hcoordinate
  exact ⟨Module.finrank k V, f.imageClosedSubgroup, ⟨e⟩⟩

/-- An algebraic group is unipotent exactly when it is algebraically
isomorphic to a closed subgroup of an upper-unitriangular group. -/
public theorem isUnipotentAlgebraicGroup_iff_upperUnitriangularIso
    {G : Variety k} [AlgebraicGroup G] :
    IsUnipotentAlgebraicGroup G ↔
      ∃ n : ℕ, ∃ H : ClosedSubgroup (uVariety k n),
        letI := H.carrierAlgebraicGroup
        Nonempty (AlgebraicGroup.Iso G H.carrierVariety) :=
  ⟨upperUnitriangularIso_of_unipotent,
    unipotent_of_upperUnitriangularIso⟩

omit [IsAlgClosed k] in
private lemma closedSubgroup_eq_of_isUnipotentRadicalSubgroup
    {G : Variety k} [AlgebraicGroup G] {U V : ClosedSubgroup G}
    (hU : IsUnipotentRadicalSubgroup U)
    (hV : IsUnipotentRadicalSubgroup V) : U = V := by
  apply SetLike.coe_injective
  ext x
  exact (hU x).trans (hV x).symm

/-- Theorem 1.5.1(b): a connected solvable algebraic group has a closed
subgroup consisting exactly of its unipotent elements. -/
public theorem exists_unipotentRadicalSubgroup_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G) :
    ∃ U : ClosedSubgroup G, IsUnipotentRadicalSubgroup U := by
  obtain ⟨n, hn, H, ⟨e⟩⟩ :=
    exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected
      hsolvable hconnected
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let P : TriangularPresentation G :=
    { n := n, positive := hn, subgroup := H, iso := e }
  exact ⟨P.unipotentRadical,
    P.mem_unipotentRadical_iff_characteristicFree⟩

/-- Theorem 1.5.1(b): the unipotent radical of a connected solvable group is
normal. -/
public theorem IsUnipotentRadicalSubgroup.normal_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    {U : ClosedSubgroup G} (hU : IsUnipotentRadicalSubgroup U) :
    U.toSubgroup.Normal := by
  obtain ⟨n, hn, H, ⟨e⟩⟩ :=
    exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected
      hsolvable hconnected
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let P : TriangularPresentation G :=
    { n := n, positive := hn, subgroup := H, iso := e }
  have hP : IsUnipotentRadicalSubgroup P.unipotentRadical :=
    P.mem_unipotentRadical_iff_characteristicFree
  rw [closedSubgroup_eq_of_isUnipotentRadicalSubgroup hU hP]
  exact P.unipotentRadical_normal

/-- Theorem 1.5.1(c): the unipotent radical of a connected solvable group is
connected. -/
public theorem IsUnipotentRadicalSubgroup.isConnected_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    {U : ClosedSubgroup G} (hU : IsUnipotentRadicalSubgroup U) :
    Variety.IsConnected U.carrierVariety := by
  obtain ⟨n, hn, H, ⟨e⟩⟩ :=
    exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected
      hsolvable hconnected
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let P : TriangularPresentation G :=
    { n := n, positive := hn, subgroup := H, iso := e }
  have hP : IsUnipotentRadicalSubgroup P.unipotentRadical :=
    P.mem_unipotentRadical_iff_characteristicFree
  rw [closedSubgroup_eq_of_isUnipotentRadicalSubgroup hU hP]
  letI : AlgebraicGroup P.unipotentRadical.carrierVariety :=
    P.unipotentRadical.carrierAlgebraicGroup
  by_cases hp : ringChar k = 0
  · have hPunipotent : IsUnipotentAlgebraicGroup
        P.unipotentRadical.carrierVariety := by
      intro z
      let x := P.unipotentRadical.inclusion.onPoints z
      have hx : x ∈ P.unipotentRadical :=
        (P.unipotentRadical.pointEquiv z).property
      have hxunipotent := (hP x).mp hx
      have hz :=
        (closedSubgroup_unipotentElement_iff P.unipotentRadical hx).mp
          hxunipotent
      have hpoint :
          P.unipotentRadical.pointEquiv.symm ⟨x, hx⟩ = z := by
        apply P.unipotentRadical.pointEquiv.injective
        rw [P.unipotentRadical.pointEquiv.apply_symm_apply]
        apply Subtype.ext
        rfl
      rw [hpoint] at hz
      exact hz
    exact hPunipotent.isConnected_of_ringChar_zero
      P.unipotentRadical.carrierVariety hp
  · let : Fact (Nat.Prime (ringChar k)) :=
      ⟨CharP.char_prime_of_ne_zero k hp⟩
    exact P.unipotentRadical_isConnected (ringChar k) hconnected

/-- Theorem 1.5.1(c): the unipotent radical of a connected solvable group is
unipotent. -/
public theorem IsUnipotentRadicalSubgroup.isUnipotent_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    {U : ClosedSubgroup G} (hU : IsUnipotentRadicalSubgroup U) :
    IsUnipotentAlgebraicGroup U.carrierVariety := by
  obtain ⟨n, hn, H, ⟨e⟩⟩ :=
    exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected
      hsolvable hconnected
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let P : TriangularPresentation G :=
    { n := n, positive := hn, subgroup := H, iso := e }
  have hP : IsUnipotentRadicalSubgroup P.unipotentRadical :=
    P.mem_unipotentRadical_iff_characteristicFree
  rw [closedSubgroup_eq_of_isUnipotentRadicalSubgroup hU hP]
  intro z
  let x := P.unipotentRadical.inclusion.onPoints z
  have hx : x ∈ P.unipotentRadical :=
    (P.unipotentRadical.pointEquiv z).property
  have hxunipotent := (hP x).mp hx
  have hz :=
    (closedSubgroup_unipotentElement_iff P.unipotentRadical hx).mp
      hxunipotent
  have hpoint :
      P.unipotentRadical.pointEquiv.symm ⟨x, hx⟩ = z := by
    apply P.unipotentRadical.pointEquiv.injective
    rw [P.unipotentRadical.pointEquiv.apply_symm_apply]
    apply Subtype.ext
    rfl
  rw [hpoint] at hz
  exact hz

end Theory.AlgebraicGroup
