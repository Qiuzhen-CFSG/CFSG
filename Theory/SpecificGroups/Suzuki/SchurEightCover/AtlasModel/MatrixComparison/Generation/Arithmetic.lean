module

public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.NativeEmbedding

/-!
# Generation of every literal root and torus over F₈

Conjugation by torus(v) gives root(v*a,0). Every nonzero element is a
power of v, and every field element is a fifth power. Squaring root(a,0)
therefore gives every central root(0,b); multiplication gives root(a,b).
The same powers of torus(v) cover the full torus. Finite arithmetic is
checked in F₈, then transported through the actual field equivalence.

This discharges full native generation in the model comparison used for
Aschbacher–Smith I.1.1 and I.1.3(5), printed p.407. The upper-right root
entry is a^6+a*b+b^4 and the Tits power is four throughout.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison.Generation

private def rootMatrix (a b : F8) : Mat :=
  !![1, a, b, a ^ 6 + a * b + b ^ 4;
     0, 1, a ^ 4, a ^ 5 + b;
     0, 0, 1, a;
     0, 0, 0, 1]

private noncomputable def rootGL (a b : F8) : GL8 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rootMatrix a b) (by
    have htri : (rootMatrix a b).BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [rootMatrix] at hij ⊢
    rw [Matrix.det_of_isUpperTriangular htri]
    simp [rootMatrix, Fin.prod_univ_four])

private theorem root_conj (a : F8) :
    torusV * rootGL a 0 * torusV⁻¹ = rootGL (v * a) 0 := by
  apply Units.ext
  exact (show ∀ a : F8,
    (torusV : Mat) * rootMatrix a 0 * ((torusV⁻¹ : GL8) : Mat) =
      rootMatrix (v * a) 0 by decide +kernel) a

private theorem root_square (a : F8) :
    rootGL a 0 * rootGL a 0 = rootGL 0 (a ^ 5) := by
  apply Units.ext
  exact (show ∀ a : F8, rootMatrix a 0 * rootMatrix a 0 = rootMatrix 0 (a ^ 5)
    by decide +kernel) a

private theorem root_mul (a b : F8) :
    rootGL a 0 * rootGL 0 b = rootGL a b := by
  apply Units.ext
  exact (show ∀ a b : F8, rootMatrix a 0 * rootMatrix 0 b = rootMatrix a b
    by decide +kernel) a b

private theorem root_zero : rootGL 0 0 = 1 := by
  apply Units.ext
  change rootMatrix 0 0 = (1 : Mat)
  decide +kernel

private theorem root_one : rootGL 1 0 = rootOne := by
  apply Units.ext
  change rootMatrix 1 0 = (rootOne : Mat)
  decide +kernel

private theorem field_power_cover :
    ∀ a : F8, a = 0 ∨ ∃ k : Fin 7, a = v ^ k.val := by decide +kernel

private theorem field_fifth_cover : ∀ b : F8, ∃ a : F8, a ^ 5 = b := by decide +kernel

private theorem root_power_mem (n : ℕ) : rootGL (v ^ n) 0 ∈ tripleSubgroup := by
  induction n with
  | zero =>
    rw [pow_zero, root_one]
    exact Subgroup.subset_closure (by simp)
  | succ n ih =>
    rw [pow_succ', ← root_conj]
    have ht : torusV ∈ tripleSubgroup := Subgroup.subset_closure (by simp)
    exact tripleSubgroup.mul_mem (tripleSubgroup.mul_mem ht ih) (tripleSubgroup.inv_mem ht)

private theorem root_first_mem (a : F8) : rootGL a 0 ∈ tripleSubgroup := by
  rcases field_power_cover a with rfl | ⟨k, rfl⟩
  · rw [root_zero]
    exact tripleSubgroup.one_mem
  · exact root_power_mem k.val

private theorem root_mem (a b : F8) : rootGL a b ∈ tripleSubgroup := by
  obtain ⟨c, rfl⟩ := field_fifth_cover b
  rw [← root_mul, ← root_square]
  exact tripleSubgroup.mul_mem (root_first_mem a)
    (tripleSubgroup.mul_mem (root_first_mem c) (root_first_mem c))

private theorem root_transport (a b : F8) :
    glEquiv (rootGL a b) = SuzukiRootGL 1 (fieldEquiv a) (fieldEquiv b) := by
  apply Units.ext
  ext i j
  change fieldEquiv (rootMatrix a b i j) =
    SuzukiRootMatrix 1 (fieldEquiv a) (fieldEquiv b) i j
  fin_cases i <;> fin_cases j <;> simp [rootMatrix, SuzukiRootMatrix]

/-- Every literal native root belongs to the transported native triple. -/
theorem native_root_mem (a b : PFAppendixIII.BinaryGaloisField 3) :
    SuzukiRootGL 1 a b ∈ tripleSubgroup.map glEquiv.toMonoidHom := by
  obtain ⟨a, rfl⟩ := fieldEquiv.surjective a
  obtain ⟨b, rfl⟩ := fieldEquiv.surjective b
  exact Subgroup.mem_map.mpr ⟨rootGL a b, root_mem a b, root_transport a b⟩

private def torusMatrix (x : F8) : Mat :=
  !![x ^ 3, 0, 0, 0; 0, x ^ 2, 0, 0;
     0, 0, (x ^ 2)⁻¹, 0; 0, 0, 0, (x ^ 3)⁻¹]

private theorem torus_step : ∀ x : F8,
    (torusV : Mat) * torusMatrix x = torusMatrix (v * x) := by decide +kernel

private theorem torus_pow (n : ℕ) :
    ((torusV ^ n : GL8) : Mat) = torusMatrix (v ^ n) := by
  induction n with
  | zero =>
    change (1 : Mat) = torusMatrix (v ^ 0)
    decide +kernel
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change (torusV : Mat) * ((torusV ^ n : GL8) : Mat) = torusMatrix (v * v ^ n)
    rw [ih, torus_step]

/-- Every literal native torus element is a power of the transported torus(v). -/
theorem native_torus_mem (x : (PFAppendixIII.BinaryGaloisField 3)ˣ) :
    SuzukiTorusGL 1 x ∈ tripleSubgroup.map glEquiv.toMonoidHom := by
  obtain ⟨a, ha⟩ := fieldEquiv.surjective (x : PFAppendixIII.BinaryGaloisField 3)
  have ha0 : a ≠ 0 := by
    intro h
    apply x.ne_zero
    rw [← ha, h, map_zero]
  obtain ⟨k, rfl⟩ := (field_power_cover a).resolve_left ha0
  have heq : glEquiv (torusV ^ k.val) = SuzukiTorusGL 1 x := by
    apply Units.ext
    ext i j
    change fieldEquiv (((torusV ^ k.val : GL8) : Mat) i j) = SuzukiTorusMatrix 1 x i j
    rw [torus_pow]
    fin_cases i <;> fin_cases j <;> simp [torusMatrix, SuzukiTorusMatrix, ← ha]
  apply Subgroup.mem_map.mpr
  exact ⟨torusV ^ k.val,
    tripleSubgroup.pow_mem (Subgroup.subset_closure (by simp)) _, heq⟩

/-- The native triple generates the entire group specified in Suzuki.lean. -/
theorem native_le_triple_map :
    SuzukiMatrixSubgroup 1 ≤ tripleSubgroup.map glEquiv.toMonoidHom := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with ⟨a, b, rfl⟩ | ⟨x, rfl⟩ | rfl
  · exact native_root_mem a b
  · exact native_torus_mem x
  · exact Subgroup.mem_map.mpr
      ⟨weyl, Subgroup.subset_closure (by simp), glEquiv_weyl⟩

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison.Generation
