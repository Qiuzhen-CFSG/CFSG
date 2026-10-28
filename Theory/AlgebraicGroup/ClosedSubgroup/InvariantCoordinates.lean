module

public import Theory.AlgebraicGroup.ClosedSubgroup.Quotient

universe u

/-! Finite-type invariant coordinates separating cosets of a closed subgroup. -/

/-! Pullback factored through the right-invariant coordinate subalgebra. -/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

@[expose]
public noncomputable def Morphism.pullbackToRightInvariantCoordinateRing
    {G I : Variety k} [AlgebraicGroup G] [AlgebraicGroup I]
    (H : ClosedSubgroup G) (φ : AlgebraicGroup.Morphism G I)
    (hφ : H.toSubgroup ≤ φ.kernel) :
    Variety.PolynomialFunction I →ₐ[k] AlgebraicGroup.rightInvariantCoordinateRing H :=
  φ.toVariety.pullbackAlgHom.codRestrict
    (AlgebraicGroup.rightInvariantCoordinateRing H)
    (fun a => by
      rw [AlgebraicGroup.mem_rightInvariantCoordinateRing_iff]
      intro g h hh
      change a (φ.onPoints (g * h)) = a (φ.onPoints g)
      rw [φ.onPoints.map_mul]
      have hhone : φ.onPoints h = 1 := hφ hh
      rw [hhone, mul_one])

/-! Evaluation of the invariant-coordinate pullback algebra homomorphism. -/

public lemma Morphism.pullbackToRightInvariantCoordinateRing_apply
    {G I : Variety k} [AlgebraicGroup G] [AlgebraicGroup I]
    (H : ClosedSubgroup G) (φ : AlgebraicGroup.Morphism G I)
    (hφ : H.toSubgroup ≤ φ.kernel) (a : Variety.PolynomialFunction I) :
    (φ.pullbackToRightInvariantCoordinateRing H hφ a).val =
      Variety.PolynomialFunction.pullback φ.toVariety a := rfl

end

/-! Finite invariant coordinates separating right cosets of a normal closed subgroup. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

public lemma ClosedSubgroup.finiteRightInvariantCoordinates_eq_iff_inv_mul_mem
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    ∃ (m : ℕ)
      (c : Fin m → Fin m → AlgebraicGroup.rightInvariantCoordinateRing H),
      ∀ g x : Variety.Point G,
        (∀ i j, (c i j).1 g = (c i j).1 x) ↔ g⁻¹ * x ∈ H.toSubgroup := by
  obtain ⟨m, F, hker⟩ := H.generalLinearMorphism_exactKernel_exists hN
  have hle : H.toSubgroup ≤ F.kernel := by
    rw [hker]
  let c : Fin m → Fin m → AlgebraicGroup.rightInvariantCoordinateRing H :=
    fun i j => F.pullbackToRightInvariantCoordinateRing H hle
      (generalLinearMatrixCoordinate m i j)
  refine ⟨m, c, ?_⟩
  intro g x
  constructor
  · intro h
    have hFx : F.onPoints g = F.onPoints x := by
      apply (glPointEquiv m).injective
      apply Units.ext
      ext i j
      have hij := h i j
      change generalLinearMatrixCoordinate m i j (F.onPoints g) =
        generalLinearMatrixCoordinate m i j (F.onPoints x) at hij
      simpa [generalLinearMatrixCoordinate_apply, glPointEquiv,
        glMatrixOfPoint] using hij
    rw [← hker]
    change F.onPoints (g⁻¹ * x) = 1
    rw [F.onPoints.map_mul, F.onPoints.map_inv, hFx, inv_mul_cancel]
  · intro hx
    have hunit : F.onPoints (g⁻¹ * x) = 1 := by
      change g⁻¹ * x ∈ F.kernel
      rwa [hker]
    have hFx : F.onPoints g = F.onPoints x := by
      rw [F.onPoints.map_mul, F.onPoints.map_inv] at hunit
      exact inv_mul_eq_one.mp hunit
    intro i j
    change generalLinearMatrixCoordinate m i j (F.onPoints g) =
      generalLinearMatrixCoordinate m i j (F.onPoints x)
    rw [hFx]

end

/-! A finite-type invariant-coordinate subalgebra separating right cosets. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

lemma ClosedSubgroup.finiteTypeRightInvariantSeparatingSubalgebra_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal) :
    ∃ C : Subalgebra k (AlgebraicGroup.rightInvariantCoordinateRing H),
      Algebra.FiniteType k C ∧
      ∀ g x : Variety.Point G,
        (∀ f : C, f.1.1 g = f.1.1 x) ↔ g⁻¹ * x ∈ H.toSubgroup := by
  obtain ⟨m, c, hc⟩ :=
    H.finiteRightInvariantCoordinates_eq_iff_inv_mul_mem hN
  let s : Set (AlgebraicGroup.rightInvariantCoordinateRing H) :=
    Set.range fun p : Fin m × Fin m => c p.1 p.2
  let C := Algebra.adjoin k s
  have hC : Algebra.FiniteType k C :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)
  refine ⟨C, hC, ?_⟩
  intro g x
  constructor
  · intro h
    apply (hc g x).mp
    intro i j
    let f : C := ⟨c i j, Algebra.subset_adjoin ⟨(i, j), rfl⟩⟩
    exact h f
  · intro hx f
    have hinv :=
      (AlgebraicGroup.mem_rightInvariantCoordinateRing_iff H f.1.1).mp
        f.1.2 g (g⁻¹ * x) hx
    symm
    simpa [← mul_assoc] using hinv

end

/-! Cofinal finite-type invariant subalgebras that still separate right cosets. -/

section

variable {k : Type u} [Field k] [IsAlgClosed k]

lemma ClosedSubgroup.finiteTypeRightInvariantSubalgebra_exists_of_finset
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hN : H.toSubgroup.Normal)
    (t : Finset (AlgebraicGroup.rightInvariantCoordinateRing H)) :
    ∃ C : Subalgebra k (AlgebraicGroup.rightInvariantCoordinateRing H),
      Algebra.FiniteType k C ∧
      (↑t : Set (AlgebraicGroup.rightInvariantCoordinateRing H)) ⊆ C ∧
      ∀ g x : Variety.Point G,
        (∀ f : C, f.1.1 g = f.1.1 x) ↔ g⁻¹ * x ∈ H.toSubgroup := by
  obtain ⟨m, c, hc⟩ :=
    H.finiteRightInvariantCoordinates_eq_iff_inv_mul_mem hN
  let s : Set (AlgebraicGroup.rightInvariantCoordinateRing H) :=
    Set.range (fun p : Fin m × Fin m => c p.1 p.2) ∪ (t : Set _)
  let C := Algebra.adjoin k s
  have hs : Set.Finite s := (Set.finite_range _).union t.finite_toSet
  have hC : Algebra.FiniteType k C :=
    Algebra.FiniteType.adjoin_of_finite hs
  refine ⟨C, hC, ?_, ?_⟩
  · intro f hf
    exact Algebra.subset_adjoin (Set.mem_union_right _ hf)
  · intro g x
    constructor
    · intro h
      apply (hc g x).mp
      intro i j
      let f : C := ⟨c i j,
        Algebra.subset_adjoin (Set.mem_union_left _ ⟨(i, j), rfl⟩)⟩
      exact h f
    · intro hx f
      have hinv :=
        (AlgebraicGroup.mem_rightInvariantCoordinateRing_iff H f.1.1).mp
          f.1.2 g (g⁻¹ * x) hx
      symm
      simpa [← mul_assoc] using hinv

end
end Theory.AlgebraicGroup
