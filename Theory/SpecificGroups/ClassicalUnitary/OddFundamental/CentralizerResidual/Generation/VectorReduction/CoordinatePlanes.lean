module

public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental.CentralizerResidual.Generation.PlaneRotations

/-!
# Special unitary actions on chosen coordinate planes

Reindex the identity-form block embedding SU₂ → SUₙ to any two distinct
coordinates. The action formula keeps the literal matrix action and shows
that every other coordinate is fixed. This is the elimination operation used
by `Generation.VectorReduction` over the original coefficient field.

Source application: Aschbacher–Smith, A.2.17, printed pp.38–39 of
`refs/quasithin.pdf`, the complementary special unitary group.
-/

open Matrix BenderSuzuki.MatrixGroups
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.OddFundamental.Generation
variable {F : Type*} [Field F] (σ : F ≃+* F) (hσ : Function.Involutive σ)

private def coordinateReindex {m n : ℕ} (e : Fin m ≃ Fin n) :
    (form σ hσ m).specialSubgroup →* (form σ hσ n).specialSubgroup :=
  let f : (form σ hσ m).specialSubgroup →* Matrix (Fin n) (Fin n) F :=
    { toFun := fun a => Matrix.reindex e e a.val.val
      map_one' := (reindexRingEquiv F e).map_one
      map_mul' := fun a b => (reindexRingEquiv F e).map_mul a.val.val b.val.val }
  f.toHomUnits.codRestrict _ fun a => by
    rw [HermitianForm.mem_specialSubgroup_iff]
    constructor
    · change (form σ hσ n).conjTranspose (Matrix.reindex e e a.val.val) * 1 *
        Matrix.reindex e e a.val.val = 1
      have hadj : (form σ hσ n).conjTranspose (Matrix.reindex e e a.val.val) =
          Matrix.reindex e e ((form σ hσ m).conjTranspose a.val.val) := by
        ext i j
        rfl
      rw [mul_one, hadj]
      change (reindexRingEquiv F e) _ * (reindexRingEquiv F e) _ = 1
      rw [← map_mul]
      have ha : (form σ hσ m).conjTranspose a.val.val * a.val.val = 1 := by
        simpa [form] using a.property.1
      rw [ha, map_one]
    · apply Units.ext
      change (Matrix.reindex e e a.val.val).det = 1
      rw [Matrix.det_reindex_self]
      exact congrArg Units.val a.property.2

private theorem block_mulVec_inl {m n : ℕ} (A : Matrix (Fin m) (Fin m) F)
    (x : Fin (m+n) → F) (i : Fin m) :
    (blockMatrix A (1 : Matrix (Fin n) (Fin n) F) *ᵥ x) (finSumFinEquiv (.inl i)) =
      (A *ᵥ (fun j => x (finSumFinEquiv (.inl j)))) i := by
  simp [blockMatrix, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv,
    Matrix.fromBlocks_mulVec, Function.comp_def]

private theorem block_mulVec_inr {m n : ℕ} (A : Matrix (Fin m) (Fin m) F)
    (x : Fin (m+n) → F) (i : Fin n) :
    (blockMatrix A (1 : Matrix (Fin n) (Fin n) F) *ᵥ x) (finSumFinEquiv (.inr i)) =
      x (finSumFinEquiv (.inr i)) := by
  simp [blockMatrix, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv,
    Matrix.fromBlocks_mulVec, Function.comp_def]

/-- An actual SU₂ homomorphism acts on any prescribed pair, fixing every other coordinate. -/
theorem exists_coordinatePlane {n : ℕ} (i j : Fin (n+2)) (hij : i ≠ j) :
    ∃ f : (form σ hσ 2).specialSubgroup →* (form σ hσ (n+2)).specialSubgroup,
      ∀ (u : (form σ hσ 2).specialSubgroup) (x : Fin (n+2) → F),
        (f u).val.val *ᵥ x = fun t =>
          if t = i then (u.val.val *ᵥ ![x i, x j]) 0
          else if t = j then (u.val.val *ᵥ ![x i, x j]) 1 else x t := by
  classical
  let E : Fin (2+n) ≃ Fin (n+2) := finCongr (Nat.add_comm 2 n)
  let v : Fin 2 → Fin (n+2) := ![i,j]
  have hv : Function.Injective v := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [v]
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair
    (fun a : Fin 2 => E (finSumFinEquiv (.inl a))) v
    (E.injective.comp (finSumFinEquiv.injective.comp Sum.inl_injective)) hv
  let e := E.trans p
  have he (a : Fin 2) : e (finSumFinEquiv (.inl a)) = v a := hp a
  let f := (coordinateReindex σ hσ e).comp (left σ hσ (m := 2) (n := n))
  refine ⟨f, fun u x => ?_⟩
  have haction (a : Fin (2+n)) :
      ((f u).val.val *ᵥ x) (e a) =
        (blockMatrix u.val.val (1 : Matrix (Fin n) (Fin n) F) *ᵥ (x ∘ e)) a := by
    change ((Matrix.reindex e e (blockMatrix u.val.val 1)) *ᵥ x) (e a) = _
    simp [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  have hvect : (fun a : Fin 2 => (x ∘ e) (finSumFinEquiv (.inl a))) = ![x i, x j] := by
    ext a
    simp only [Function.comp_apply, he]
    fin_cases a <;> rfl
  ext t
  obtain ⟨a, rfl⟩ := e.surjective t
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
  rw [haction]
  cases a with
  | inl a =>
    rw [block_mulVec_inl, hvect, he]
    fin_cases a <;> simp [v, hij.symm]
  | inr a =>
    rw [block_mulVec_inr]
    have hi : e (finSumFinEquiv (.inr a)) ≠ i := by
      rw [← show e (finSumFinEquiv (.inl (0 : Fin 2))) = i from he 0]
      exact fun h => Sum.inr_ne_inl (finSumFinEquiv.injective (e.injective h))
    have hj : e (finSumFinEquiv (.inr a)) ≠ j := by
      rw [← show e (finSumFinEquiv (.inl (1 : Fin 2))) = j from he 1]
      exact fun h => Sum.inr_ne_inl (finSumFinEquiv.injective (e.injective h))
    rw [if_neg hi, if_neg hj]
    rfl

end Theory.SpecificGroups.ClassicalUnitary.OddFundamental.Generation
