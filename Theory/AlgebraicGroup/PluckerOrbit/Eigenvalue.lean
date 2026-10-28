module

public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Theory.AlgebraicGroup.Irreducible.Product
public import Theory.AlgebraicGroup.PluckerOrbit.Conjugation

universe u v w

/-! Zero sets of polynomial functions are Zariski closed. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma Variety.PolynomialFunction.zeroSet_isClosed
    {V : Variety k} (f : V.PolynomialFunction) :
    IsClosed {x : Variety.Point V | f x = 0} := by
  rw [Variety.isClosed_iff_isZariskiClosed]
  rcases f.representedBy with ⟨p, hp⟩
  refine ⟨{p}, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
  rw [← hp x]

end

/-! Regular coordinates of the affine Plücker orbit. -/

section

open scoped ExteriorAlgebra BigOperators

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingPluckerOrbitCoordinate
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i : Fin (Fintype.card H.rightTranslateVanishingExteriorIndex)) :
    G.PolynomialFunction :=
  ∑ j, algebraMap k G.PolynomialFunction
      (H.rightTranslateVanishingExteriorBasis.repr
        H.rightTranslateVanishingPluckerVector j) *
    H.rightTranslateVanishingExteriorFinMatrixCoefficient i j

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitCoordinate_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (i : Fin (Fintype.card H.rightTranslateVanishingExteriorIndex))
    (g : Variety.Point G) :
    H.rightTranslateVanishingPluckerOrbitCoordinate i g =
      H.rightTranslateVanishingExteriorBasis.repr
        (H.rightTranslateVanishingPluckerOrbitVector g) i := by
  rw [ClosedSubgroup.rightTranslateVanishingPluckerOrbitCoordinate]
  let ev : G.PolynomialFunction →+* k :=
    { toFun := fun f => f g
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ j, algebraMap k G.PolynomialFunction
      (H.rightTranslateVanishingExteriorBasis.repr
        H.rightTranslateVanishingPluckerVector j) *
    H.rightTranslateVanishingExteriorFinMatrixCoefficient i j) = _
  rw [map_sum]
  have heval : (∑ j, ev (algebraMap k G.PolynomialFunction
      (H.rightTranslateVanishingExteriorBasis.repr
        H.rightTranslateVanishingPluckerVector j) *
    H.rightTranslateVanishingExteriorFinMatrixCoefficient i j)) =
      ∑ j, (H.rightTranslateVanishingExteriorBasis.repr
        H.rightTranslateVanishingPluckerVector j) *
      H.rightTranslateVanishingExteriorFinMatrixCoefficient i j g := by
    apply Finset.sum_congr rfl
    intro j hj
    change (algebraMap k G.PolynomialFunction
        (H.rightTranslateVanishingExteriorBasis.repr
          H.rightTranslateVanishingPluckerVector j)) g *
      (H.rightTranslateVanishingExteriorFinMatrixCoefficient i j) g = _
    rw [polynomialFunction_algebraMap_apply]
  rw [heval]
  simp_rw [← H.rightTranslateVanishingExteriorRepresentationMatrix_apply]
  exact H.rightTranslateVanishingExteriorRepresentationMatrix_mul_repr_eq_pluckerOrbit i g

end

/-! Regular equations for eigensets on the affine Plücker orbit. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingPluckerOrbitEigenvalueEquation
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (h : Variety.Point G) (a : k)
    (i : Fin (Fintype.card H.rightTranslateVanishingExteriorIndex)) :
    G.PolynomialFunction :=
  Variety.PolynomialFunction.pullback (AlgebraicGroup.leftMulMorphism G h)
      (H.rightTranslateVanishingPluckerOrbitCoordinate i) -
    algebraMap k G.PolynomialFunction a *
      H.rightTranslateVanishingPluckerOrbitCoordinate i

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitEigenvalueEquation_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (h g : Variety.Point G) (a : k)
    (i : Fin (Fintype.card H.rightTranslateVanishingExteriorIndex)) :
    H.rightTranslateVanishingPluckerOrbitEigenvalueEquation h a i g =
      H.rightTranslateVanishingExteriorBasis.repr
        (H.rightTranslateVanishingPluckerOrbitVector (h * g)) i -
      a * H.rightTranslateVanishingExteriorBasis.repr
        (H.rightTranslateVanishingPluckerOrbitVector g) i := by
  rw [ClosedSubgroup.rightTranslateVanishingPluckerOrbitEigenvalueEquation]
  change H.rightTranslateVanishingPluckerOrbitCoordinate i
      ((AlgebraicGroup.leftMulMorphism G h).toFun g) -
    (algebraMap k G.PolynomialFunction a) g *
      H.rightTranslateVanishingPluckerOrbitCoordinate i g = _
  rw [AlgebraicGroup.leftMulMorphism_apply,
    polynomialFunction_algebraMap_apply,
    H.rightTranslateVanishingPluckerOrbitCoordinate_apply,
    H.rightTranslateVanishingPluckerOrbitCoordinate_apply]

end

/-! Closed eigensets of normal elements on the affine Plücker orbit. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingPluckerOrbitEigenvalueSet
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (h : Variety.Point G) (a : k) : Set (Variety.Point G) :=
  ⋂ i, {g |
    H.rightTranslateVanishingPluckerOrbitEigenvalueEquation h a i g = 0}

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitEigenvalueSet_isClosed
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (h : Variety.Point G) (a : k) :
    IsClosed (H.rightTranslateVanishingPluckerOrbitEigenvalueSet h a) := by
  rw [ClosedSubgroup.rightTranslateVanishingPluckerOrbitEigenvalueSet]
  exact isClosed_iInter fun i =>
    (H.rightTranslateVanishingPluckerOrbitEigenvalueEquation h a i).zeroSet_isClosed

end

/-! Multiplication in a linear-representation orbit. -/

section

variable {k : Type u} [Field k]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} [AddCommGroup V] [Module k V]

public lemma linearRepresentationOrbitVector_mul
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V) (v : V) (h g : Γ) :
    linearRepresentationOrbitVector ρ v (h * g) =
      ((ρ h : LinearMap.GeneralLinearGroup k V) : Module.End k V)
        (linearRepresentationOrbitVector ρ v g) := by
  rw [linearRepresentationOrbitVector, linearRepresentationOrbitVector]
  rw [map_mul]
  rfl

end

/-! Multiplication in the affine Plücker orbit. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitVector_mul
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (h g : Variety.Point G) :
    H.rightTranslateVanishingPluckerOrbitVector (h * g) =
      ((H.rightTranslateVanishingExteriorGeneralLinear h :
        LinearMap.GeneralLinearGroup k
          (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan)) :
        Module.End k
          (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan))
        (H.rightTranslateVanishingPluckerOrbitVector g) := by
  exact linearRepresentationOrbitVector_mul
    H.rightTranslateVanishingExteriorGeneralLinear
    H.rightTranslateVanishingPluckerVector h g

end

/-! Vector characterization of affine Plücker eigensets. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitEigenvalueSet_mem_iff
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (h g : Variety.Point G) (a : k) :
    g ∈ H.rightTranslateVanishingPluckerOrbitEigenvalueSet h a ↔
      a • H.rightTranslateVanishingPluckerOrbitVector g =
        ((H.rightTranslateVanishingExteriorGeneralLinear h :
          LinearMap.GeneralLinearGroup k
            (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
              H.rightTranslateVanishingSpan)) :
          Module.End k
            (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
              H.rightTranslateVanishingSpan))
          (H.rightTranslateVanishingPluckerOrbitVector g) := by
  constructor
  · intro hg
    apply H.rightTranslateVanishingExteriorBasis.repr.injective
    ext i
    have hi := Set.mem_iInter.mp hg i
    change H.rightTranslateVanishingPluckerOrbitEigenvalueEquation h a i g = 0 at hi
    rw [H.rightTranslateVanishingPluckerOrbitEigenvalueEquation_apply] at hi
    rw [map_smul]
    rw [← H.rightTranslateVanishingPluckerOrbitVector_mul]
    exact (sub_eq_zero.mp hi).symm
  · intro hg
    rw [ClosedSubgroup.rightTranslateVanishingPluckerOrbitEigenvalueSet]
    apply Set.mem_iInter.mpr
    intro i
    change H.rightTranslateVanishingPluckerOrbitEigenvalueEquation h a i g = 0
    rw [H.rightTranslateVanishingPluckerOrbitEigenvalueEquation_apply]
    apply sub_eq_zero.mpr
    rw [H.rightTranslateVanishingPluckerOrbitVector_mul]
    simpa using congrArg
      (fun x => H.rightTranslateVanishingExteriorBasis.repr x i) hg.symm

end

/-! Nonvanishing of vectors in a general-linear orbit. -/

section

variable {k : Type u} [Field k]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} [AddCommGroup V] [Module k V]

public lemma linearRepresentationOrbitVector_ne_zero
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V) {v : V} (hv : v ≠ 0) (g : Γ) :
    linearRepresentationOrbitVector ρ v g ≠ 0 := by
  intro hzero
  apply hv
  apply (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ g)).injective
  simpa [linearRepresentationOrbitVector] using hzero

end

/-! Nonvanishing of affine Plücker orbit vectors. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitVector_ne_zero
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (g : Variety.Point G) :
    H.rightTranslateVanishingPluckerOrbitVector g ≠ 0 :=
  linearRepresentationOrbitVector_ne_zero
    H.rightTranslateVanishingExteriorGeneralLinear
    H.rightTranslateVanishingPluckerVector_ne_zero g

end

/-! Normal line stabilizers act by scalars on every vector in the orbit. -/

section

variable {k : Type u} [Field k]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} [AddCommGroup V] [Module k V]

public lemma normalLineStabilizer_orbitVector_eigenvector
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V) (v : V) (H : Subgroup Γ)
    (hN : H.Normal)
    (hstab : ∀ q : Γ,
      q ∈ H ↔ linearRepresentationOrbitVector ρ v q ∈ k ∙ v)
    {h : Γ} (hh : h ∈ H) (g : Γ) :
    ∃ a : k, a • linearRepresentationOrbitVector ρ v g =
      ((ρ h : LinearMap.GeneralLinearGroup k V) : Module.End k V)
        (linearRepresentationOrbitVector ρ v g) := by
  let q := g⁻¹ * h * g
  have hq : q ∈ H := hN.conj_mem' h hh g
  have hline : ∃ a : k, a • v = linearRepresentationOrbitVector ρ v q := by
    rw [← Submodule.mem_span_singleton]
    exact (hstab q).1 hq
  rcases hline with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  change a • (((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V) v) =
    ((ρ h : LinearMap.GeneralLinearGroup k V) : Module.End k V)
      (((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V) v)
  calc
    a • (((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V) v) =
        ((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V) (a • v) := by
          rw [map_smul]
    _ = ((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V)
        (linearRepresentationOrbitVector ρ v q) := by rw [ha]
    _ = ((((ρ g) * (ρ q) : LinearMap.GeneralLinearGroup k V) : Module.End k V) v) := rfl
    _ = ((((ρ h) * (ρ g) : LinearMap.GeneralLinearGroup k V) : Module.End k V) v) := by
      congr 2
      rw [← map_mul, ← map_mul]
      simp only [q, ← mul_assoc, mul_inv_cancel, one_mul]
    _ = ((ρ h : LinearMap.GeneralLinearGroup k V) : Module.End k V)
        (((ρ g : LinearMap.GeneralLinearGroup k V) : Module.End k V) v) := rfl

end

/-! Pointwise eigenvalues for a normal subgroup on the affine Plücker orbit. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbit_exists_eigenvalue
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) {h : Variety.Point G} (hh : h ∈ H.toSubgroup)
    (g : Variety.Point G) :
    ∃ a : k, a • H.rightTranslateVanishingPluckerOrbitVector g =
      ((H.rightTranslateVanishingExteriorGeneralLinear h :
        LinearMap.GeneralLinearGroup k
          (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan)) :
        Module.End k
          (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
            H.rightTranslateVanishingSpan))
        (H.rightTranslateVanishingPluckerOrbitVector g) := by
  apply normalLineStabilizer_orbitVector_eigenvector
    H.rightTranslateVanishingExteriorGeneralLinear
    H.rightTranslateVanishingPluckerVector H.toSubgroup hN
  · intro q
    rw [linearRepresentationOrbitVector,
      H.rightTranslateVanishingExteriorGeneralLinear_apply]
    exact (H.chevalleyPluckerLine_stabilizer_iff q).symm
  · exact hh

end

/-! Producing an eigenvalue from a nonzero scalar eigen-equation. -/

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V]

public lemma Module.End.hasEigenvalue_of_smul_eq
    (f : Module.End k V) (a : k) (v : V) (hv : v ≠ 0)
    (ha : a • v = f v) : f.HasEigenvalue a := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
  rw [Module.End.hasEigenvector_iff]
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    exact ha.symm
  · exact hv

/-! Eigenvalues occur among the characteristic-polynomial roots. -/

variable {k : Type u} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]

public lemma Module.End.hasEigenvalue_mem_charpoly_roots
    (f : Module.End k V) (a : k) (ha : f.HasEigenvalue a) :
    a ∈ f.charpoly.roots := by
  rw [Polynomial.mem_roots f.charpoly_monic.ne_zero]
  exact (Module.End.hasEigenvalue_iff_isRoot_charpoly f a).mp ha

/-! The affine Plücker orbit is covered by finitely many eigensets. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitEigenvalueSet_finite_cover
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) {h : Variety.Point G} (hh : h ∈ H.toSubgroup) :
    ∃ A : Finset k, (Set.univ : Set (Variety.Point G)) ⊆
      ⋃ a ∈ A, H.rightTranslateVanishingPluckerOrbitEigenvalueSet h a := by
  classical
  let f : Module.End k
      (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
        H.rightTranslateVanishingSpan) :=
    ((H.rightTranslateVanishingExteriorGeneralLinear h :
      LinearMap.GeneralLinearGroup k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan)) :
      Module.End k
        (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan))
  refine ⟨f.charpoly.roots.toFinset, ?_⟩
  intro g hg
  rcases H.rightTranslateVanishingPluckerOrbit_exists_eigenvalue hN hh g with ⟨a, ha⟩
  have haeigen : f.HasEigenvalue a :=
    Module.End.hasEigenvalue_of_smul_eq f a
      (H.rightTranslateVanishingPluckerOrbitVector g)
      (H.rightTranslateVanishingPluckerOrbitVector_ne_zero g) ha
  have haroot : a ∈ f.charpoly.roots :=
    Module.End.hasEigenvalue_mem_charpoly_roots f a haeigen
  refine Set.mem_iUnion.mpr ⟨a, ?_⟩
  refine Set.mem_iUnion.mpr ⟨Multiset.mem_toFinset.mpr haroot, ?_⟩
  exact (H.rightTranslateVanishingPluckerOrbitEigenvalueSet_mem_iff h g a).2 ha

end

/-! Finite closed covers of irreducible sets. -/

variable {X : Type u} [TopologicalSpace X]

public lemma IsIrreducible.exists_subset_of_finset_iUnion_closed
    {s : Set X} (hs : IsIrreducible s) (t : Finset (Set X))
    (hclosed : ∀ z ∈ t, IsClosed z) (hcover : s ⊆ ⋃₀ (t : Set (Set X))) :
    ∃ z ∈ t, s ⊆ z :=
  isIrreducible_iff_sUnion_isClosed.mp hs t hclosed hcover

/-! A connected affine Plücker orbit has one global eigenvalue. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitEigenvalueSet_univ_subset
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hG : Variety.IsConnected G) (hN : H.toSubgroup.Normal)
    {h : Variety.Point G} (hh : h ∈ H.toSubgroup) :
    ∃ a : k, (Set.univ : Set (Variety.Point G)) ⊆
      H.rightTranslateVanishingPluckerOrbitEigenvalueSet h a := by
  classical
  rcases H.rightTranslateVanishingPluckerOrbitEigenvalueSet_finite_cover hN hh with
    ⟨A, hcover⟩
  let t : Finset (Set (Variety.Point G)) :=
    A.image (fun a => H.rightTranslateVanishingPluckerOrbitEigenvalueSet h a)
  have htclosed : ∀ z ∈ t, IsClosed z := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    exact H.rightTranslateVanishingPluckerOrbitEigenvalueSet_isClosed h a
  have htscover : (Set.univ : Set (Variety.Point G)) ⊆
      ⋃₀ (t : Set (Set (Variety.Point G))) := by
    intro g hg
    have hgu := hcover hg
    rw [Set.mem_iUnion] at hgu
    rcases hgu with ⟨a, hgu⟩
    rw [Set.mem_iUnion] at hgu
    rcases hgu with ⟨ha, hga⟩
    exact Set.mem_sUnion_of_mem hga
      (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, ha, rfl⟩))
  have hirr := connectedAlgebraicGroup_irreducible G hG
  rcases IsIrreducible.exists_subset_of_finset_iUnion_closed
      hirr t htclosed htscover with ⟨z, hz, huz⟩
  rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
  exact ⟨a, huz⟩

end

/-! Uniform scalar action on the affine Plücker orbit of a connected group. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbit_uniform_eigenvalue
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hG : Variety.IsConnected G) (hN : H.toSubgroup.Normal)
    {h : Variety.Point G} (hh : h ∈ H.toSubgroup) :
    ∃ a : k, ∀ g : Variety.Point G,
      a • H.rightTranslateVanishingPluckerOrbitVector g =
        ((H.rightTranslateVanishingExteriorGeneralLinear h :
          LinearMap.GeneralLinearGroup k
            (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
              H.rightTranslateVanishingSpan)) :
          Module.End k
            (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
              H.rightTranslateVanishingSpan))
          (H.rightTranslateVanishingPluckerOrbitVector g) := by
  rcases H.rightTranslateVanishingPluckerOrbitEigenvalueSet_univ_subset
    hG hN hh with ⟨a, ha⟩
  refine ⟨a, fun g => ?_⟩
  exact (H.rightTranslateVanishingPluckerOrbitEigenvalueSet_mem_iff h g a).1
    (ha (Set.mem_univ g))

end

/-! Extending a scalar orbit equation to the span of the orbit. -/

section

variable {k : Type u} [Field k]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} [AddCommGroup V] [Module k V]

public lemma linearRepresentationOrbitSpan_smul_eq
    (ρ : Γ →* LinearMap.GeneralLinearGroup k V) (v : V)
    (h : Γ) (a : k)
    (horbit : ∀ g : Γ, a • linearRepresentationOrbitVector ρ v g =
      ((ρ h : LinearMap.GeneralLinearGroup k V) : Module.End k V)
        (linearRepresentationOrbitVector ρ v g))
    {x : V} (hx : x ∈ linearRepresentationOrbitSpan ρ v) :
    a • x = ((ρ h : LinearMap.GeneralLinearGroup k V) : Module.End k V) x := by
  refine Submodule.span_induction (p := fun x _ =>
    a • x = ((ρ h : LinearMap.GeneralLinearGroup k V) : Module.End k V) x) ?_ ?_ ?_ ?_ hx
  · intro x hx
    rcases hx with ⟨g, rfl⟩
    exact horbit g
  · simp
  · intro x y hx hy hxe hye
    simp [hxe, hye]
  · intro r x hx hxe
    rw [map_smul, ← hxe, smul_smul, smul_smul, mul_comm]

end

/-! Uniform scalar action on the affine Plücker orbit span. -/

section

open scoped ExteriorAlgebra

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpan_uniform_eigenvalue
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hG : Variety.IsConnected G) (hN : H.toSubgroup.Normal)
    {h : Variety.Point G} (hh : h ∈ H.toSubgroup) :
    ∃ a : k, ∀ x :
        ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
          H.rightTranslateVanishingSpan,
      x ∈ H.rightTranslateVanishingPluckerOrbitSpan →
      a • x =
        ((H.rightTranslateVanishingExteriorGeneralLinear h :
          LinearMap.GeneralLinearGroup k
            (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
              H.rightTranslateVanishingSpan)) :
          Module.End k
            (⋀[k]^H.rightTranslateVanishingTopWedgeData.degree
              H.rightTranslateVanishingSpan)) x := by
  rcases H.rightTranslateVanishingPluckerOrbit_uniform_eigenvalue
    hG hN hh with ⟨a, ha⟩
  refine ⟨a, fun x hx => Theory.AlgebraicGroup.linearRepresentationOrbitSpan_smul_eq
    H.rightTranslateVanishingExteriorGeneralLinear
    H.rightTranslateVanishingPluckerVector h a ha hx⟩

end

section
variable {k : Type u} [Field k] [IsAlgClosed k]

set_option maxHeartbeats 800000 in
omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanGeneralLinear_eq_smul_id_of_mem
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hG : Variety.IsConnected G) (hN : H.toSubgroup.Normal)
    {g : Variety.Point G} (hg : g ∈ H.toSubgroup) :
    ∃ a : k,
      ((H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear g :
        LinearMap.GeneralLinearGroup k H.rightTranslateVanishingPluckerOrbitSpan) :
        Module.End k H.rightTranslateVanishingPluckerOrbitSpan) = a • LinearMap.id := by
  let hu := H.rightTranslateVanishingPluckerOrbitSpan_uniform_eigenvalue hG hN hg
  let a := Classical.choose hu
  have ha := Classical.choose_spec hu
  refine ⟨a, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear_apply_coe]
  exact (ha x x.property).symm
end

/-! The connected-case reverse inclusion for the Plücker-conjugation kernel. -/

section
open scoped ExteriorAlgebra
variable {k : Type u} [Field k] [IsAlgClosed k]

set_option maxHeartbeats 800000 in
omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerConjugationMorphism_eq_one_of_mem_of_connected
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hG : Variety.IsConnected G) (hN : H.toSubgroup.Normal)
    {g : Variety.Point G} (hg : g ∈ H.toSubgroup) :
    H.rightTranslateVanishingPluckerConjugationMorphism.onPoints g = 1 := by
  let hu := @ClosedSubgroup.rightTranslateVanishingPluckerOrbitSpanGeneralLinear_eq_smul_id_of_mem
    k _ G _ H hG hN g hg
  let a := Classical.choose hu
  have hscalarρ_direct := Classical.choose_spec hu
  let W : Type u := H.rightTranslateVanishingPluckerOrbitSpan
  let n := Module.finrank k W
  let b : Module.Basis (Fin (Module.finrank k W)) k W :=
    H.rightTranslateVanishingPluckerOrbitSpanBasis
  let ρ : Variety.Point G →* LinearMap.GeneralLinearGroup k W :=
    H.rightTranslateVanishingPluckerOrbitSpanGeneralLinear
  let p := H.rightTranslateVanishingPluckerOrbitSpanRepresentationMorphism.onPoints g
  have hp : p = generalLinearRepresentationPoint (k := k) (V := W) b (ρ g) := by
    simpa [p, b, ρ] using
      H.rightTranslateVanishingPluckerOrbitSpanRepresentationMorphism_apply g
  have hscalarρ : ((ρ g : LinearMap.GeneralLinearGroup k W) : Module.End k W) =
      a • LinearMap.id := by
    simpa [ρ, W] using hscalarρ_direct
  have hscalarReverse :
      ((generalLinearPointRepresentation (k := k) (Module.finrank k W)
        (generalLinearRepresentationPoint (k := k) (V := W) b (ρ g)) :
          LinearMap.GeneralLinearGroup k (Fin (Module.finrank k W) → k)) :
        Module.End k (Fin (Module.finrank k W) → k)) = a • LinearMap.id := by
    let nW := Module.finrank k W
    let s := generalLinearStandardIndexEquiv (k := k) nW
    let bs := generalLinearStandardBasis (k := k) nW
    let q := generalLinearRepresentationPoint (k := k) (V := W) b (ρ g)
    let ρs := generalLinearPointRepresentation (k := k) nW q
    apply bs.ext
    intro j
    apply bs.repr.injective
    ext i
    let pidx := s.symm i
    let qidx := s.symm j
    have hq := generalLinearPointRepresentation_matrixCoefficient
      (k := k) nW q i j
    have hpoint := generalLinearRepresentationPoint_matrix
      (k := k) (V := W) b (ρ g) pidx qidx
    have hxv := LinearMap.congr_fun hscalarρ (b qidx)
    have hx := congrArg (fun y : W => b.repr y pidx) hxv
    calc
      bs.repr ((ρs : Module.End k (Fin nW → k)) (bs j)) i =
          q.val (Sum.inl (pidx, qidx)) := by simpa [pidx, qidx, s] using hq
      _ = b.repr (((ρ g : LinearMap.GeneralLinearGroup k W) : Module.End k W)
          (b qidx)) pidx := hpoint
      _ = b.repr ((a • LinearMap.id) (b qidx)) pidx := hx
      _ = bs.repr ((a • LinearMap.id) (bs j)) i := by
        simp [bs, s, pidx, qidx, Finsupp.single_apply]
  have hbase : (generalLinearConjugationMorphism (k := k) n).onPoints
      (generalLinearRepresentationPoint (k := k) (V := W) b (ρ g)) = 1 := by
    rw [generalLinearConjugationMorphism_apply,
      generalLinearRepresentationPoint_eq_one_iff,
      generalLinearConjugationPointRepresentation_apply,
      generalLinearConjugationRepresentation_eq_one_iff]
    exact ⟨a, hscalarReverse⟩
  have hcomp : (generalLinearConjugationMorphism (k := k) n).onPoints p = 1 := by
    rw [hp]
    exact hbase
  exact (H.rightTranslateVanishingPluckerConjugationMorphism_apply g).trans hcomp

end

/-! The connected-case kernel equality for the Plücker-conjugation morphism. -/

section
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
public lemma ClosedSubgroup.rightTranslateVanishingPluckerConjugationMorphism_kernel_eq_of_connected
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hG : Variety.IsConnected G) (hN : H.toSubgroup.Normal) :
    H.rightTranslateVanishingPluckerConjugationMorphism.kernel = H.toSubgroup := by
  ext g
  constructor
  · intro hg
    exact H.rightTranslateVanishingPluckerConjugationMorphism_eq_one_imp_mem g
      (MonoidHom.mem_ker.mp hg)
  · intro hg
    exact MonoidHom.mem_ker.mpr
      (H.rightTranslateVanishingPluckerConjugationMorphism_eq_one_of_mem_of_connected
        hG hN hg)

end
end Theory.AlgebraicGroup
