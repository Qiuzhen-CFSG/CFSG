module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.NormalizerAction.MonomialGeometry

/-!
# The full normalizer of a unitary frame torus

A generator of the norm-one group supplies the regular diagonal matrix
`diag(u,1,u⁻¹)`. If a matrix normalizes the torus, conjugating this element
by its inverse gives another diagonal matrix. The resulting intertwining
identity and the distinct eigenvalues force a single nonzero entry in every
column. Applying the same argument to the inverse proves preservation of
the punctured coordinate axes. Conversely the literal permutation formula
proves that every frame monomial matrix normalizes the torus.

The projective statement follows from exact lifting of normalizers through
the full scalar kernel. Source: GLS4, Chapter 4, Lemma 3.11(c), used in
Chapter 2, Lemma 17.4. This geometric part works for every fixed-field size
at least two, independently of the characteristic.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.IdentityGram HermitianForm.EvenInner
open scoped Pointwise
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E]

theorem gl_column_nonzero (g : GL (Fin 3) E) (i : Fin 3) : ∃ j, g.val j i ≠ 0 := by
  by_contra h
  push Not at h
  have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i i) (Units.inv_mul g)
  simp [Matrix.mul_apply, h] at he

theorem coordinate_mem_of_column_support (g : GL (Fin 3) E)
    (hg : ∀ i, ∃ j, g.val j i ≠ 0 ∧ ∀ k, k ≠ j → g.val k i = 0)
    {v : Fin 3 → E} (hv : v ∈ OddThreeLocal.Monomial.coordinateVectors) :
    g • v ∈ OddThreeLocal.Monomial.coordinateVectors := by
  obtain ⟨i, hi, hv⟩ := hv
  have he : v = Pi.single i (v i) := by
    ext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj, hv j hj]
  obtain ⟨j, hj, hg⟩ := hg i
  rw [he]
  refine ⟨j, ?_, ?_⟩
  · change (g.val *ᵥ Pi.single i (v i)) j ≠ 0
    simpa using mul_ne_zero hj hi
  · intro k hk
    change (g.val *ᵥ Pi.single i (v i)) k = 0
    simp [hg k hk]

theorem mem_coordinateStabilizer_of_column_support (g : GL (Fin 3) E)
    (hg : ∀ i, ∃ j, g.val j i ≠ 0 ∧ ∀ k, k ≠ j → g.val k i = 0)
    (hgi : ∀ i, ∃ j, g⁻¹.val j i ≠ 0 ∧ ∀ k, k ≠ j → g⁻¹.val k i = 0) :
    g ∈ coordinateStabilizer := by
  apply MulAction.mem_stabilizer_iff.mpr
  apply Set.Subset.antisymm
  · rintro v hv
    obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.mp hv
    exact coordinate_mem_of_column_support g hg hw
  · intro v hv
    exact Set.mem_smul_set.mpr ⟨g⁻¹ • v, coordinate_mem_of_column_support g⁻¹ hgi hv,
      smul_inv_smul g v⟩

theorem column_support_of_diagonal_intertwining (g : GL (Fin 3) E)
    (a b : Fin 3 → Eˣ) (ha : Function.Injective a)
    (h : diagonalHom a * g = g * diagonalHom b) (j : Fin 3) :
    ∃ i, g.val i j ≠ 0 ∧ ∀ k, k ≠ i → g.val k j = 0 := by
  obtain ⟨i, hi⟩ := gl_column_nonzero g j
  refine ⟨i, hi, ?_⟩
  have he (k : Fin 3) : (a k : E) * g.val k j = g.val k j * (b j : E) := by
    have hh := congrArg (fun M : GL (Fin 3) E => M.val k j) h
    simpa only [Units.val_mul, diagonalHom, MonoidHom.coe_mk, OneHom.coe_mk,
      Matrix.diagonal_mul, Matrix.mul_diagonal] using hh
  have hi' : a i = b j := Units.ext (mul_right_cancel₀ hi (by
    simpa only [mul_comm] using he i))
  intro k hk
  by_contra hk'
  have hk'' : a k = b j := Units.ext (mul_right_cancel₀ hk' (by
    simpa only [mul_comm] using he k))
  exact hk (ha (hk''.trans hi'.symm))

theorem exists_regular_pair [Finite E] (J : HermitianForm 3 E) (q : ℕ)
    (hq : 2 ≤ q) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    ∃ x : normOne J × normOne J, Function.Injective (pairDiagonal J x) := by
  obtain ⟨u, hu⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp
    (inferInstance : IsCyclic (normOne J))
  rw [normOne_card J hcard
    (BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J q hcard hfixed)] at hu
  have h1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    omega
  have h2 : u ≠ u⁻¹ := by
    intro h
    have hs : u ^ 2 = 1 := by
      rw [pow_two]
      calc u * u = u⁻¹ * u := congrArg (fun a => a * u) h
           _ = 1 := inv_mul_cancel u
    have hd := orderOf_dvd_of_pow_eq_one hs
    rw [hu] at hd
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  refine ⟨(u, 1), ?_⟩
  have h1u : u.val ≠ 1 := fun h => h1 (Subtype.ext h)
  have h2u : u.val ≠ u.val⁻¹ := fun h => h2 (Subtype.ext h)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [pairDiagonal, eq_comm, inv_eq_one]

theorem specialFrameMonomial_le_normalizer (J : HermitianForm 3 E)
    (P : OrthogonalFrame J) : specialFrameMonomial J P ≤ normalizer (specialFrameTorus J P) := by
  intro g hg
  exact (specialMonomialAction_action J P ⟨g, hg⟩).mem_normalizer J P g _

theorem specialFrameTorus_normalizer_eq_monomial [Finite E]
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hq : 2 ≤ q) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    normalizer (specialFrameTorus J P) = specialFrameMonomial J P := by
  apply le_antisymm _ (specialFrameMonomial_le_normalizer J P)
  obtain ⟨x, hx⟩ := exists_regular_pair J q hq hcard hfixed
  have hpair (y : normOne J × normOne J) :
      frameCoordinateHom J P (specialPairHom J P y) = diagonalHom (pairDiagonal J y) := by
    change P.val⁻¹ * (P.val * diagonalHom (pairDiagonal J y) * P.val⁻¹) * (P.val⁻¹)⁻¹ = _
    simp [mul_assoc]
  have hcol (g : J.specialSubgroup) (hg : g ∈ normalizer (specialFrameTorus J P)) :
      ∀ j, ∃ i, (frameCoordinateHom J P g).val i j ≠ 0 ∧
        ∀ k, k ≠ i → (frameCoordinateHom J P g).val k j = 0 := by
    have hm : g⁻¹ * specialPairHom J P x * g ∈ specialFrameTorus J P :=
      (Subgroup.mem_normalizer_iff''.mp hg _).mp
        (specialPairHom_range J P ▸ (show specialPairHom J P x ∈ (specialPairHom J P).range from ⟨x, rfl⟩))
    obtain ⟨b, hb⟩ := hm
    change diagonalHom b = frameCoordinateHom J P (g⁻¹ * specialPairHom J P x * g) at hb
    rw [map_mul, map_mul, map_inv, hpair] at hb
    have he : diagonalHom (pairDiagonal J x) * frameCoordinateHom J P g =
        frameCoordinateHom J P g * diagonalHom b := by
      rw [hb]
      simp [mul_assoc]
    exact column_support_of_diagonal_intertwining _ _ _ hx he
  intro g hg
  apply mem_coordinateStabilizer_of_column_support _ (hcol g hg)
  have hgi : g⁻¹ ∈ normalizer (specialFrameTorus J P) :=
    inv_mem hg
  simpa only [map_inv] using hcol g⁻¹ hgi

theorem projectiveFrameTorus_normalizer_eq_monomial [Finite E]
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hq : 2 ≤ q) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    normalizer (projectiveFrameTorus J P) = projectiveFrameMonomial J P := by
  rw [projectiveFrameMonomial, ← specialFrameTorus_normalizer_eq_monomial J P q hq hcard hfixed,
    ← projectiveFrameTorus_normalizer_comap, Subgroup.map_comap_eq_self_of_surjective
      J.specialToProjective_surjective]

end UnitaryThree.OddTorusNormalizer
