module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.PolynomialChart

/-!
# Extreme charts of a projective monomial curve

The binomial relations of a monomial parametrization show that its scheme-image
closure is covered by the two occupied extreme-coordinate basic opens. This
controls every scheme point, and is the projective boundary calculation in the
direct torus-curve proof of Borel, Linear Algebraic Groups, §13.13.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] {ι : Type} [Finite ι]

omit [Finite ι] in
private theorem coordinates_adjoin :
    Algebra.adjoin (projectiveGrading k ι 0)
      (Set.range (MvPolynomial.X : ι → MvPolynomial ι k)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C r =>
      simpa using (Algebra.adjoin (projectiveGrading k ι 0)
        (Set.range (MvPolynomial.X : ι → MvPolynomial ι k))).algebraMap_mem
        ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C ι r⟩
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | mul_X p i hp => exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ⟨i, rfl⟩)

omit [Finite ι] in
noncomputable def extremeRelation (c : ι → k) (n : ι → ℕ) (N : ℕ) (a b j : ι) :
    MvPolynomial ι k :=
  MvPolynomial.C (c a ^ (N - n j) * c b ^ n j) * MvPolynomial.X j ^ N -
    MvPolynomial.C (c j ^ N) * MvPolynomial.X a ^ (N - n j) * MvPolynomial.X b ^ n j

omit [Finite ι] in
theorem extremeRelation_isHomogeneous (c : ι → k) (n : ι → ℕ) (N : ℕ) (a b j : ι)
    (hn : n j ≤ N) : (extremeRelation c n N a b j).IsHomogeneous N := by
  unfold extremeRelation
  apply MvPolynomial.IsHomogeneous.sub
  · exact MvPolynomial.isHomogeneous_C_mul_X_pow _ _ _
  · simpa only [Nat.sub_add_cancel hn] using
      (MvPolynomial.isHomogeneous_C_mul_X_pow (c j ^ N) a (N - n j)).mul
        (MvPolynomial.isHomogeneous_X_pow b (n j))

omit [Finite ι] in
theorem extreme_charts_of_relations
    (P : Proj (projectiveGrading k ι)) (c : ι → k) (n : ι → ℕ)
    (N : ℕ) (hN : 0 < N) (a b : ι) (ha : c a ≠ 0) (hb : c b ≠ 0)
    (hzero : ∀ j, c j = 0 → MvPolynomial.X j ∈ P.asHomogeneousIdeal)
    (hrel : ∀ j, c j ≠ 0 → extremeRelation c n N a b j ∈ P.asHomogeneousIdeal) :
    P ∈ Proj.basicOpen (projectiveGrading k ι) (MvPolynomial.X a) ⊔
      Proj.basicOpen (projectiveGrading k ι) (MvPolynomial.X b) := by
  classical
  by_contra h
  have haP : MvPolynomial.X a ∈ P.asHomogeneousIdeal := by
    by_contra hh
    exact h (Or.inl hh)
  have hbP : MvPolynomial.X b ∈ P.asHomogeneousIdeal := by
    by_contra hh
    exact h (Or.inr hh)
  have hall (j : ι) : MvPolynomial.X j ∈ P.asHomogeneousIdeal := by
    by_cases hj : c j = 0
    · exact hzero j hj
    have hr := hrel j hj
    have hright : MvPolynomial.C (c j ^ N) * MvPolynomial.X a ^ (N - n j) *
        MvPolynomial.X b ^ n j ∈ P.asHomogeneousIdeal.toIdeal := by
      by_cases hja : n j < N
      · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
          (Ideal.pow_mem_of_mem _ haP _ (Nat.sub_pos_of_lt hja)))
      · have hjpos : 0 < n j := lt_of_lt_of_le hN (Nat.le_of_not_gt hja)
        exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hbP _ hjpos)
    have hleft : MvPolynomial.C (c a ^ (N - n j) * c b ^ n j) *
        MvPolynomial.X j ^ N ∈ P.asHomogeneousIdeal.toIdeal := by
      exact (P.asHomogeneousIdeal.toIdeal.sub_mem_iff_left hright).mp hr
    have hconst : MvPolynomial.C (c a ^ (N - n j) * c b ^ n j) ∉
        P.asHomogeneousIdeal.toIdeal := by
      intro hh
      apply P.isPrime.ne_top
      exact Ideal.eq_top_of_isUnit_mem _ hh
        ((isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb))).map
          (MvPolynomial.C : k →+* MvPolynomial ι k))
    exact (P.isPrime.pow_mem_iff_mem N hN).mp
      ((P.isPrime.mem_or_mem hleft).resolve_left hconst)
  have htop := Proj.iSup_basicOpen_eq_top' (projectiveGrading k ι) MvPolynomial.X
    (fun i => ⟨1, MvPolynomial.isHomogeneous_X k i⟩) coordinates_adjoin
  have hP : P ∈ ⨆ i, Proj.basicOpen (projectiveGrading k ι) (MvPolynomial.X i) := by
    rw [htop]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hP
  exact hi (hall i)

open SeparatingBorel.ProjectiveLimit

omit [Finite ι] in
theorem extremeRelation_aeval (c : ι → k) (n : ι → ℕ) (N : ℕ) (a b j : ι)
    (ha : n a = 0) (hb : n b = N) :
    MvPolynomial.aeval (monomialCoordinates c n) (extremeRelation c n N a b j) = 0 := by
  simp only [extremeRelation, map_sub, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_pow, monomialCoordinates, ha, hb, pow_zero, mul_one,
    Polynomial.algebraMap_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, mul_pow, ← pow_mul, Nat.mul_comm (n j) N]
  ring

/-- The two occupied extreme coordinates cover the actual scheme-image closure
of a projective monomial parametrization. -/
theorem monomial_closure_extreme_charts
    (c : ι → k) (n : ι → ℕ) (N : ℕ) (hN : 0 < N) (a b : ι)
    (ha : n a = 0) (hb : n b = N) (hca : c a ≠ 0) (hcb : c b ≠ 0)
    (hbound : ∀ j, n j ≤ N) :
    closure (Set.range (monomialCurve c n ⟨a, ha, hca⟩).hom) ⊆
      (Proj.basicOpen (projectiveGrading k ι) (MvPolynomial.X a) ⊔
        Proj.basicOpen (projectiveGrading k ι) (MvPolynomial.X b) :
          Set (Proj (projectiveGrading k ι))) := by
  intro P hP
  apply extreme_charts_of_relations P c n N hN a b hca hcb
  · intro j hj
    have hh := curve_closure_vanishes (monomialCoordinates c n)
      (monomialCoordinates_unit c n ⟨a, ha, hca⟩) (MvPolynomial.X j) 1
      Nat.zero_lt_one (MvPolynomial.isHomogeneous_X k j)
      (by simp [monomialCoordinates, hj]) hP
    exact Classical.not_not.mp hh
  · intro j _
    have hh := curve_closure_vanishes (monomialCoordinates c n)
      (monomialCoordinates_unit c n ⟨a, ha, hca⟩) (extremeRelation c n N a b j) N hN
      (extremeRelation_isHomogeneous c n N a b j (hbound j))
      (extremeRelation_aeval c n N a b j ha hb) hP
    exact Classical.not_not.mp hh

end Theory.AlgebraicGroup.Bor1.FlagCurve
