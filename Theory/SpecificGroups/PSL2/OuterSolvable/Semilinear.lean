module

public import Theory.SpecificGroups.PSL2.OuterSolvable.Actions
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Solvable outer quotients from actual semilinear coverage

The units of the field and its field automorphisms form a solvable semidirect
product. The diagonal/field conjugation identity maps this product into
`Aut(PSL₂)`, and then into the actual quotient by inner automorphisms.
If every automorphism is inner times diagonal times field, this last map is
surjective. No splitting of the diagonal extension is needed.

This is the solvability consequence of the A₁ case of GLS3, Theorem 2.5.12
(`refs/KGroup/GLS3/chapter2.tex`). Coverage remains an explicit input here,
including in characteristic odd and at field cardinality nine.
-/

namespace Theory.PSL2.OuterSolvable

variable {K : Type*} [Field K]

/-- The concrete group of diagonal and field parameters. -/
public abbrev SemilinearParameters (K : Type*) [Field K] :=
  Kˣ ⋊[fieldUnitsAction] (K ≃+* K)

/-- The actual diagonal and field actions combine to a group homomorphism. -/
@[expose] public def semilinearAutHom : SemilinearParameters K →* MulAut (Group K) :=
  SemidirectProduct.lift diagonalAutHom projectiveFieldAutHom (fun σ => by
    apply MonoidHom.ext
    intro u
    exact diagonal_field_covariance σ u)

/-- Composing the concrete action with the quotient by inner automorphisms. -/
@[expose] public def semilinearOuterHom : SemilinearParameters K →* MulAut.Outer (Group K) :=
  (QuotientGroup.mk' (MulAut.innerSubgroup (Group K))).comp semilinearAutHom

/-- The parameter group is an extension of abelian units by a cyclic field group. -/
public theorem semilinearParameters_isSolvable [Finite K] :
    Group.IsSolvable (SemilinearParameters K) := by
  let : Group.IsSolvable (K ≃+* K) := finiteFieldAut_isSolvable
  exact Group.isSolvable_of_ker_le_range SemidirectProduct.inl
    SemidirectProduct.rightHom SemidirectProduct.range_inl_eq_ker_rightHom.ge

/-- Inner-diagonal-field coverage gives a surjection from the solvable parameter group
onto the actual outer automorphism group. -/
public theorem semilinearOuterHom_surjective_of_coverage
    (hcoverage : ∀ a : MulAut (Group K), ∃ (g : Group K) (u : Kˣ) (σ : K ≃+* K),
      a = MulAut.conj g * diagonalAutHom u * projectiveFieldAutHom σ) :
    Function.Surjective (semilinearOuterHom (K := K)) := by
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup (Group K)) x
  obtain ⟨g, u, σ, ha⟩ := hcoverage a
  refine ⟨⟨u, σ⟩, ?_⟩
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Group K))
  change q (diagonalAutHom u * projectiveFieldAutHom σ) = q a
  have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
  simp only [ha, map_mul, hg, one_mul]

/-- Conditional solvability, with coverage stated for actual matrix automorphisms. -/
public theorem outer_isSolvable_of_semilinear_coverage [Finite K]
    (hcoverage : ∀ a : MulAut (Group K), ∃ (g : Group K) (u : Kˣ) (σ : K ≃+* K),
      a = MulAut.conj g * diagonalAutHom u * projectiveFieldAutHom σ) :
    Group.IsSolvable (MulAut.Outer (Group K)) := by
  let : Group.IsSolvable (SemilinearParameters K) := semilinearParameters_isSolvable
  exact Group.isSolvable_of_surjective (semilinearOuterHom_surjective_of_coverage hcoverage)

/-- In characteristic two only inner and field factors are needed. -/
public theorem outer_isSolvable_of_field_coverage [Finite K] [CharP K 2]
    (hcoverage : ∀ a : MulAut (Group K), ∃ (g : Group K) (σ : K ≃+* K),
      a = MulAut.conj g * fieldAut σ) :
    Group.IsSolvable (MulAut.Outer (Group K)) := by
  apply outer_isSolvable_of_semilinear_coverage
  intro a
  obtain ⟨g, σ, ha⟩ := hcoverage a
  refine ⟨g, 1, σ, ?_⟩
  simpa only [map_one, mul_one, projectiveFieldAutHom_eq_fieldAut] using ha

end Theory.PSL2.OuterSolvable
