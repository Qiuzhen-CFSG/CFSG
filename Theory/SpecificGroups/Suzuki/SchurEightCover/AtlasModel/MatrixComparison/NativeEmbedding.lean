module

public import Theory.SpecificGroups.Suzuki.SchurEightCover.AtlasModel.MatrixComparison.ForwardWords

/-!
# Embedding the explicit matrix pair into the native Suzuki group

Entrywise field transport sends the checked native triple to the literal
root, torus and Weyl generators in `BenderSuzuki.MatrixGroups.Suzuki`.
The checked forward words therefore put both displayed matrices, and their
whole generated subgroup, in the native Suzuki group. The resulting map is
injective. Its surjectivity remains the full-generation obligation.

Source: the model comparison used for Aschbacher–Smith I.1.1 and I.1.3(5),
printed p.407; numerical attribution is retained in `source/README.md`.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison

noncomputable def nativeV : (PFAppendixIII.BinaryGaloisField 3)ˣ :=
  Units.map fieldEquiv.toMonoidHom vUnit

@[simp] theorem nativeV_val : (nativeV : PFAppendixIII.BinaryGaloisField 3) =
    fieldEquiv v := rfl

theorem glEquiv_rootOne : glEquiv rootOne = SuzukiRootGL 1 1 0 := by
  apply Units.ext
  ext i j
  change fieldEquiv (rootOne i j) = SuzukiRootMatrix 1 1 0 i j
  fin_cases i <;> fin_cases j <;> simp [rootOne, code, SuzukiRootMatrix]

theorem glEquiv_torusV : glEquiv torusV = SuzukiTorusGL 1 nativeV := by
  have ht : (torusV : Mat) =
      !![v ^ 3, 0, 0, 0; 0, v ^ 2, 0, 0;
         0, 0, (v ^ 2)⁻¹, 0; 0, 0, 0, (v ^ 3)⁻¹] := by decide +kernel
  apply Units.ext
  ext i j
  change fieldEquiv ((torusV : Mat) i j) = SuzukiTorusMatrix 1 nativeV i j
  rw [ht]
  fin_cases i <;> fin_cases j <;> simp [SuzukiTorusMatrix]

theorem glEquiv_weyl : glEquiv weyl = SuzukiWeylGL 1 := by
  apply Units.ext
  ext i j
  change fieldEquiv (weyl i j) = SuzukiWeylMatrix 1 i j
  fin_cases i <;> fin_cases j <;> simp [weyl, code, SuzukiWeylMatrix]

theorem tripleSubgroup_le_native :
    tripleSubgroup ≤ (SuzukiMatrixSubgroup 1).comap glEquiv.toMonoidHom := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  change glEquiv g ∈ SuzukiMatrixSubgroup 1
  apply Subgroup.subset_closure
  rcases hg with rfl | hg
  · exact Or.inl ⟨1, 0, glEquiv_rootOne⟩
  · rcases hg with rfl | hg
    · exact Or.inr (Or.inl ⟨nativeV, glEquiv_torusV⟩)
    · obtain rfl := Set.mem_singleton_iff.mp hg
      exact Or.inr (Or.inr glEquiv_weyl)

theorem pairSubgroup_le_native :
    pairSubgroup ≤ (SuzukiMatrixSubgroup 1).comap glEquiv.toMonoidHom :=
  pairSubgroup_le_triple.trans tripleSubgroup_le_native

/-- The actual inclusion of the displayed matrix subgroup in native Sz(8). -/
noncomputable def nativeEmbedding : PairModel →* SuzukiMatrixGroup 1 where
  toFun g := ⟨glEquiv g.val, pairSubgroup_le_native g.property⟩
  map_one' := Subtype.ext glEquiv.map_one
  map_mul' g h := Subtype.ext (glEquiv.map_mul g.val h.val)

theorem nativeEmbedding_injective : Function.Injective nativeEmbedding := by
  intro g h heq
  apply Subtype.ext
  exact glEquiv.injective (congrArg Subtype.val heq)

/-- The first generator retains its literal displayed matrix. -/
theorem nativeEmbedding_pairA : (nativeEmbedding pairA).val = glEquiv matrixA := rfl

/-- The second generator retains its literal displayed matrix. -/
theorem nativeEmbedding_pairB : (nativeEmbedding pairB).val = glEquiv matrixB := rfl

end BenderSuzuki.MatrixGroups.SchurEightCover.AtlasModel.MatrixComparison
