module

public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.Sparse

/-!
# The binary orbit and the sparse spanning family

The explicit change of generators below is verified in the natural tensor cube
by tensor bilinearity and arithmetic in characteristic two. Both inclusions of
spans are proved, without using linear independence or a dimension assertion.
Source: the concrete construction for GLS3 2.8.7 and 2.8.10(g).
-/

@[expose] public noncomputable section
namespace Atlas.G2.Restricted.Steinberg.OrbitClosure
open scoped TensorProduct
variable (F : Type*) [Field F] [CharP F 2]
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

/-- Enumerate the six binary parameters in lexicographic order. -/
def binaryIndex (j : Fin 64) : BinaryIndex := fun i => j.val.testBit (5-i.val)

theorem binaryIndex_surjective : Function.Surjective binaryIndex := by
  intro t
  cases h0 : t 0 <;> cases h1 : t 1 <;> cases h2 : t 2 <;>
    cases h3 : t 3 <;> cases h4 : t 4 <;> cases h5 : t 5
  · refine ⟨0, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨1, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨2, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨3, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨4, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨5, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨6, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨7, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨8, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨9, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨10, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨11, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨12, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨13, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨14, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨15, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨16, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨17, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨18, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨19, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨20, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨21, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨22, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨23, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨24, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨25, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨26, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨27, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨28, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨29, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨30, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨31, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨32, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨33, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨34, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨35, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨36, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨37, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨38, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨39, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨40, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨41, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨42, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨43, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨44, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨45, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨46, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨47, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨48, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨49, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨50, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨51, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨52, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨53, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨54, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨55, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨56, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨57, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨58, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨59, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨60, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨61, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨62, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  · refine ⟨63, ?_⟩
    funext i
    fin_cases i
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm


/-- The longest Weyl element carries the two seed factors to `e₅,e₄`. -/
theorem orbit_eq_xy (j : Fin 64) :
    binaryOrbitVector F (binaryIndex j) =
      pure F (NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex j))) (e F 5))
        (NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex j))) (e F 5))
        (NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex j))) (e F 4)) +
      pure F (NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex j))) (e F 5))
        (NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex j))) (e F 4))
        (NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex j))) (e F 5)) := by
  simp only [binaryOrbitVector, seed, map_add, ambientAction_pure, map_mul,
    Module.End.mul_apply, longestWeyl, pow_succ, pow_zero, mul_one, map_one,
    Module.End.one_apply, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]

theorem orbit_0 : binaryOrbitVector F (binaryIndex 0) =
    b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 0))) (e F 5) =
      e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 0))) (e F 4) =
      e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_1 : binaryOrbitVector F (binaryIndex 1) =
    b49 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 1))) (e F 5) =
      e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 1))) (e F 4) =
      e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b49, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_2 : binaryOrbitVector F (binaryIndex 2) =
    b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 2))) (e F 5) =
      e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 2))) (e F 4) =
      e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_3 : binaryOrbitVector F (binaryIndex 3) =
    b35 F + b48 F + b49 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 3))) (e F 5) =
      e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 3))) (e F 4) =
      e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b35, b48, b49, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_4 : binaryOrbitVector F (binaryIndex 4) =
    b27 F + b31 F + b33 F + b54 F + b58 F + b60 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 4))) (e F 5) =
      e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 4))) (e F 4) =
      e F 1 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b27, b31, b33, b54, b58, b60, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_5 : binaryOrbitVector F (binaryIndex 5) =
    b8 F + b11 F + b27 F + b31 F + b33 F + b40 F + b44 F + b46 F + b49 F + b54 F + b58 F + b60 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 5))) (e F 5) =
      e F 1 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 5))) (e F 4) =
      e F 1 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b8, b11, b27, b31, b33, b40, b44, b46, b49, b54, b58, b60, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_6 : binaryOrbitVector F (binaryIndex 6) =
    b27 F + b31 F + b33 F + b35 F + b54 F + b58 F + b60 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 6))) (e F 5) =
      e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 6))) (e F 4) =
      e F 1 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b27, b31, b33, b35, b54, b58, b60, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_7 : binaryOrbitVector F (binaryIndex 7) =
    b8 F + b11 F + b40 F + b44 F + b46 F + b48 F + b49 F + b54 F + b58 F + b60 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 7))) (e F 5) =
      e F 1 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 7))) (e F 4) =
      e F 1 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b8, b11, b40, b44, b46, b48, b49, b54, b58, b60, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_8 : binaryOrbitVector F (binaryIndex 8) =
    b1 F + b3 F + b51 F + b55 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 8))) (e F 5) =
      e F 0 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 8))) (e F 4) =
      e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b1, b3, b51, b55, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_9 : binaryOrbitVector F (binaryIndex 9) =
    b1 F + b3 F + b13 F + b17 F + b22 F + b37 F + b41 F + b47 F + b49 F + b51 F + b55 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 9))) (e F 5) =
      e F 0 + e F 2 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 9))) (e F 4) =
      e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b1, b3, b13, b17, b22, b37, b41, b47, b49, b51, b55, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_10 : binaryOrbitVector F (binaryIndex 10) =
    b0 F + b1 F + b2 F + b3 F + b50 F + b51 F + b53 F + b55 F + b60 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 10))) (e F 5) =
      e F 0 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 10))) (e F 4) =
      e F 1 + e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b1, b2, b3, b50, b51, b53, b55, b60, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_11 : binaryOrbitVector F (binaryIndex 11) =
    b0 F + b1 F + b2 F + b3 F + b4 F + b5 F + b7 F + b9 F + b11 F + b12 F + b13 F + b15 F + b17 F + b21 F + b22 F + b23 F + b24 F + b26 F + b28 F + b33 F + b34 F + b35 F + b36 F + b37 F + b39 F + b41 F + b46 F + b47 F + b48 F + b49 F + b50 F + b51 F + b53 F + b55 F + b60 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 11))) (e F 5) =
      e F 0 + e F 1 + e F 2 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 11))) (e F 4) =
      e F 1 + e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b1, b2, b3, b4, b5, b7, b9, b11, b12, b13, b15, b17, b21, b22, b23, b24, b26, b28, b33, b34, b35, b36, b37, b39, b41, b46, b47, b48, b49, b50, b51, b53, b55, b60, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_12 : binaryOrbitVector F (binaryIndex 12) =
    b0 F + b1 F + b3 F + b4 F + b5 F + b6 F + b8 F + b9 F + b11 F + b23 F + b24 F + b25 F + b27 F + b28 F + b29 F + b31 F + b33 F + b34 F + b50 F + b51 F + b52 F + b54 F + b55 F + b56 F + b58 F + b60 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 12))) (e F 5) =
      e F 0 + e F 1 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 12))) (e F 4) =
      e F 1 + e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b1, b3, b4, b5, b6, b8, b9, b11, b23, b24, b25, b27, b28, b29, b31, b33, b34, b50, b51, b52, b54, b55, b56, b58, b60, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_13 : binaryOrbitVector F (binaryIndex 13) =
    b0 F + b1 F + b3 F + b12 F + b13 F + b14 F + b16 F + b17 F + b18 F + b21 F + b22 F + b23 F + b24 F + b25 F + b27 F + b28 F + b29 F + b31 F + b33 F + b34 F + b36 F + b37 F + b38 F + b40 F + b41 F + b42 F + b44 F + b46 F + b47 F + b49 F + b50 F + b51 F + b52 F + b54 F + b55 F + b56 F + b58 F + b60 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 13))) (e F 5) =
      e F 0 + e F 2 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 13))) (e F 4) =
      e F 1 + e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b1, b3, b12, b13, b14, b16, b17, b18, b21, b22, b23, b24, b25, b27, b28, b29, b31, b33, b34, b36, b37, b38, b40, b41, b42, b44, b46, b47, b49, b50, b51, b52, b54, b55, b56, b58, b60, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_14 : binaryOrbitVector F (binaryIndex 14) =
    b1 F + b2 F + b3 F + b5 F + b6 F + b7 F + b8 F + b9 F + b24 F + b25 F + b26 F + b27 F + b28 F + b29 F + b31 F + b34 F + b35 F + b51 F + b52 F + b53 F + b54 F + b55 F + b56 F + b58 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 14))) (e F 5) =
      e F 0 + e F 1 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 14))) (e F 4) =
      e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b1, b2, b3, b5, b6, b7, b8, b9, b24, b25, b26, b27, b28, b29, b31, b34, b35, b51, b52, b53, b54, b55, b56, b58, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_15 : binaryOrbitVector F (binaryIndex 15) =
    b1 F + b2 F + b3 F + b5 F + b6 F + b7 F + b8 F + b9 F + b13 F + b14 F + b15 F + b16 F + b17 F + b18 F + b22 F + b37 F + b38 F + b39 F + b40 F + b41 F + b42 F + b44 F + b47 F + b48 F + b49 F + b51 F + b52 F + b53 F + b54 F + b55 F + b56 F + b58 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 15))) (e F 5) =
      e F 0 + e F 1 + e F 2 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 15))) (e F 4) =
      e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b1, b2, b3, b5, b6, b7, b8, b9, b13, b14, b15, b16, b17, b18, b22, b37, b38, b39, b40, b41, b42, b44, b47, b48, b49, b51, b52, b53, b54, b55, b56, b58, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_16 : binaryOrbitVector F (binaryIndex 16) =
    b19 F + b57 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 16))) (e F 5) =
      e F 2 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 16))) (e F 4) =
      e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b19, b57, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_17 : binaryOrbitVector F (binaryIndex 17) =
    b19 F + b43 F + b49 F + b57 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 17))) (e F 5) =
      e F 2 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 17))) (e F 4) =
      e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b19, b43, b49, b57, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_18 : binaryOrbitVector F (binaryIndex 18) =
    b13 F + b19 F + b20 F + b51 F + b57 F + b59 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 18))) (e F 5) =
      e F 2 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 18))) (e F 4) =
      e F 0 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b13, b19, b20, b51, b57, b59, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_19 : binaryOrbitVector F (binaryIndex 19) =
    b1 F + b13 F + b19 F + b20 F + b24 F + b30 F + b32 F + b35 F + b37 F + b43 F + b45 F + b48 F + b49 F + b51 F + b57 F + b59 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 19))) (e F 5) =
      e F 0 + e F 2 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 19))) (e F 4) =
      e F 0 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b1, b13, b19, b20, b24, b30, b32, b35, b37, b43, b45, b48, b49, b51, b57, b59, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_20 : binaryOrbitVector F (binaryIndex 20) =
    b0 F + b3 F + b12 F + b14 F + b16 F + b17 F + b19 F + b21 F + b23 F + b25 F + b27 F + b28 F + b30 F + b31 F + b33 F + b50 F + b52 F + b54 F + b55 F + b57 F + b58 F + b60 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 20))) (e F 5) =
      e F 0 + e F 2 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 20))) (e F 4) =
      e F 1 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b3, b12, b14, b16, b17, b19, b21, b23, b25, b27, b28, b30, b31, b33, b50, b52, b54, b55, b57, b58, b60, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_21 : binaryOrbitVector F (binaryIndex 21) =
    b0 F + b3 F + b4 F + b6 F + b8 F + b9 F + b11 F + b12 F + b14 F + b16 F + b17 F + b19 F + b21 F + b23 F + b25 F + b27 F + b28 F + b30 F + b31 F + b33 F + b36 F + b38 F + b40 F + b41 F + b43 F + b44 F + b46 F + b49 F + b50 F + b52 F + b54 F + b55 F + b57 F + b58 F + b60 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 21))) (e F 5) =
      e F 0 + e F 1 + e F 2 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 21))) (e F 4) =
      e F 1 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b3, b4, b6, b8, b9, b11, b12, b14, b16, b17, b19, b21, b23, b25, b27, b28, b30, b31, b33, b36, b38, b40, b41, b43, b44, b46, b49, b50, b52, b54, b55, b57, b58, b60, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_22 : binaryOrbitVector F (binaryIndex 22) =
    b0 F + b1 F + b3 F + b12 F + b13 F + b14 F + b16 F + b17 F + b19 F + b20 F + b21 F + b23 F + b24 F + b25 F + b27 F + b28 F + b30 F + b31 F + b32 F + b33 F + b35 F + b50 F + b51 F + b52 F + b54 F + b55 F + b57 F + b58 F + b59 F + b60 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 22))) (e F 5) =
      e F 0 + e F 2 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 22))) (e F 4) =
      e F 0 + e F 1 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b1, b3, b12, b13, b14, b16, b17, b19, b20, b21, b23, b24, b25, b27, b28, b30, b31, b32, b33, b35, b50, b51, b52, b54, b55, b57, b58, b59, b60, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_23 : binaryOrbitVector F (binaryIndex 23) =
    b4 F + b5 F + b6 F + b8 F + b9 F + b10 F + b11 F + b12 F + b13 F + b14 F + b16 F + b17 F + b19 F + b20 F + b21 F + b36 F + b37 F + b38 F + b40 F + b41 F + b43 F + b44 F + b45 F + b46 F + b48 F + b49 F + b50 F + b51 F + b52 F + b54 F + b55 F + b57 F + b58 F + b59 F + b60 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 23))) (e F 5) =
      e F 1 + e F 2 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 23))) (e F 4) =
      e F 0 + e F 1 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b4, b5, b6, b8, b9, b10, b11, b12, b13, b14, b16, b17, b19, b20, b21, b36, b37, b38, b40, b41, b43, b44, b45, b46, b48, b49, b50, b51, b52, b54, b55, b57, b58, b59, b60, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_24 : binaryOrbitVector F (binaryIndex 24) =
    b1 F + b3 F + b13 F + b17 F + b19 F + b22 F + b51 F + b55 F + b57 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 24))) (e F 5) =
      e F 0 + e F 2 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 24))) (e F 4) =
      e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b1, b3, b13, b17, b19, b22, b51, b55, b57, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_25 : binaryOrbitVector F (binaryIndex 25) =
    b1 F + b3 F + b37 F + b41 F + b43 F + b47 F + b49 F + b51 F + b55 F + b57 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 25))) (e F 5) =
      e F 0 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 25))) (e F 4) =
      e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b1, b3, b37, b41, b43, b47, b49, b51, b55, b57, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_26 : binaryOrbitVector F (binaryIndex 26) =
    b0 F + b2 F + b3 F + b12 F + b14 F + b15 F + b17 F + b19 F + b20 F + b21 F + b22 F + b50 F + b52 F + b53 F + b55 F + b57 F + b59 F + b60 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 26))) (e F 5) =
      e F 0 + e F 2 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 26))) (e F 4) =
      e F 0 + e F 1 + e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b2, b3, b12, b14, b15, b17, b19, b20, b21, b22, b50, b52, b53, b55, b57, b59, b60, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_27 : binaryOrbitVector F (binaryIndex 27) =
    b4 F + b6 F + b7 F + b9 F + b10 F + b11 F + b23 F + b25 F + b26 F + b28 F + b30 F + b32 F + b33 F + b34 F + b35 F + b36 F + b38 F + b39 F + b41 F + b43 F + b45 F + b46 F + b47 F + b48 F + b49 F + b50 F + b52 F + b53 F + b55 F + b57 F + b59 F + b60 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 27))) (e F 5) =
      e F 1 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 27))) (e F 4) =
      e F 0 + e F 1 + e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b4, b6, b7, b9, b10, b11, b23, b25, b26, b28, b30, b32, b33, b34, b35, b36, b38, b39, b41, b43, b45, b46, b47, b48, b49, b50, b52, b53, b55, b57, b59, b60, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_28 : binaryOrbitVector F (binaryIndex 28) =
    b8 F + b11 F + b16 F + b18 F + b19 F + b21 F + b22 F + b27 F + b29 F + b30 F + b31 F + b33 F + b34 F + b54 F + b56 F + b57 F + b58 F + b60 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 28))) (e F 5) =
      e F 1 + e F 2 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 28))) (e F 4) =
      e F 1 + e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b8, b11, b16, b18, b19, b21, b22, b27, b29, b30, b31, b33, b34, b54, b56, b57, b58, b60, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_29 : binaryOrbitVector F (binaryIndex 29) =
    b27 F + b29 F + b30 F + b31 F + b33 F + b34 F + b40 F + b42 F + b43 F + b44 F + b46 F + b47 F + b49 F + b54 F + b56 F + b57 F + b58 F + b60 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 29))) (e F 5) =
      e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 29))) (e F 4) =
      e F 1 + e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b27, b29, b30, b31, b33, b34, b40, b42, b43, b44, b46, b47, b49, b54, b56, b57, b58, b60, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_30 : binaryOrbitVector F (binaryIndex 30) =
    b4 F + b5 F + b6 F + b7 F + b8 F + b10 F + b12 F + b13 F + b14 F + b15 F + b16 F + b18 F + b19 F + b20 F + b22 F + b23 F + b24 F + b25 F + b26 F + b27 F + b29 F + b30 F + b31 F + b32 F + b34 F + b35 F + b50 F + b51 F + b52 F + b53 F + b54 F + b56 F + b57 F + b58 F + b59 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 30))) (e F 5) =
      e F 1 + e F 2 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 30))) (e F 4) =
      e F 0 + e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b4, b5, b6, b7, b8, b10, b12, b13, b14, b15, b16, b18, b19, b20, b22, b23, b24, b25, b26, b27, b29, b30, b31, b32, b34, b35, b50, b51, b52, b53, b54, b56, b57, b58, b59, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_31 : binaryOrbitVector F (binaryIndex 31) =
    b0 F + b1 F + b2 F + b4 F + b5 F + b6 F + b7 F + b8 F + b10 F + b36 F + b37 F + b38 F + b39 F + b40 F + b42 F + b43 F + b44 F + b45 F + b47 F + b48 F + b49 F + b50 F + b51 F + b52 F + b53 F + b54 F + b56 F + b57 F + b58 F + b59 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 31))) (e F 5) =
      e F 0 + e F 1 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 31))) (e F 4) =
      e F 0 + e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (0 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b1, b2, b4, b5, b6, b7, b8, b10, b36, b37, b38, b39, b40, b42, b43, b44, b45, b47, b48, b49, b50, b51, b52, b53, b54, b56, b57, b58, b59, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_32 : binaryOrbitVector F (binaryIndex 32) =
    b4 F + b10 F + b50 F + b56 F + b59 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 32))) (e F 5) =
      e F 1 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 32))) (e F 4) =
      e F 0 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b4, b10, b50, b56, b59, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_33 : binaryOrbitVector F (binaryIndex 33) =
    b0 F + b4 F + b10 F + b36 F + b42 F + b45 F + b49 F + b50 F + b56 F + b59 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 33))) (e F 5) =
      e F 0 + e F 1 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 33))) (e F 4) =
      e F 0 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b4, b10, b36, b42, b45, b49, b50, b56, b59, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_34 : binaryOrbitVector F (binaryIndex 34) =
    b4 F + b8 F + b10 F + b50 F + b54 F + b56 F + b59 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 34))) (e F 5) =
      e F 1 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 34))) (e F 4) =
      e F 0 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b4, b8, b10, b50, b54, b56, b59, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_35 : binaryOrbitVector F (binaryIndex 35) =
    b0 F + b4 F + b8 F + b10 F + b23 F + b27 F + b29 F + b32 F + b35 F + b36 F + b40 F + b42 F + b45 F + b48 F + b49 F + b50 F + b54 F + b56 F + b59 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 35))) (e F 5) =
      e F 0 + e F 1 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 35))) (e F 4) =
      e F 0 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b4, b8, b10, b23, b27, b29, b32, b35, b36, b40, b42, b45, b48, b49, b50, b54, b56, b59, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_36 : binaryOrbitVector F (binaryIndex 36) =
    b4 F + b7 F + b8 F + b10 F + b11 F + b23 F + b26 F + b27 F + b29 F + b31 F + b32 F + b33 F + b50 F + b53 F + b54 F + b56 F + b58 F + b59 F + b60 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 36))) (e F 5) =
      e F 1 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 36))) (e F 4) =
      e F 0 + e F 1 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b4, b7, b8, b10, b11, b23, b26, b27, b29, b31, b32, b33, b50, b53, b54, b56, b58, b59, b60, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_37 : binaryOrbitVector F (binaryIndex 37) =
    b0 F + b2 F + b23 F + b26 F + b27 F + b29 F + b31 F + b32 F + b33 F + b36 F + b39 F + b40 F + b42 F + b44 F + b45 F + b46 F + b49 F + b50 F + b53 F + b54 F + b56 F + b58 F + b59 F + b60 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 37))) (e F 5) =
      e F 0 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 37))) (e F 4) =
      e F 0 + e F 1 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b2, b23, b26, b27, b29, b31, b32, b33, b36, b39, b40, b42, b44, b45, b46, b49, b50, b53, b54, b56, b58, b59, b60, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_38 : binaryOrbitVector F (binaryIndex 38) =
    b4 F + b7 F + b10 F + b11 F + b23 F + b26 F + b29 F + b31 F + b32 F + b33 F + b35 F + b50 F + b53 F + b56 F + b58 F + b59 F + b60 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 38))) (e F 5) =
      e F 1 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 38))) (e F 4) =
      e F 0 + e F 1 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b4, b7, b10, b11, b23, b26, b29, b31, b32, b33, b35, b50, b53, b56, b58, b59, b60, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_39 : binaryOrbitVector F (binaryIndex 39) =
    b0 F + b2 F + b36 F + b39 F + b42 F + b44 F + b45 F + b46 F + b48 F + b49 F + b50 F + b53 F + b56 F + b58 F + b59 F + b60 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 39))) (e F 5) =
      e F 0 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 39))) (e F 4) =
      e F 0 + e F 1 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b2, b36, b39, b42, b44, b45, b46, b48, b49, b50, b53, b56, b58, b59, b60, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_40 : binaryOrbitVector F (binaryIndex 40) =
    b0 F + b1 F + b3 F + b4 F + b5 F + b6 F + b9 F + b10 F + b50 F + b51 F + b52 F + b55 F + b56 F + b59 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 40))) (e F 5) =
      e F 0 + e F 1 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 40))) (e F 4) =
      e F 0 + e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b1, b3, b4, b5, b6, b9, b10, b50, b51, b52, b55, b56, b59, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_41 : binaryOrbitVector F (binaryIndex 41) =
    b4 F + b5 F + b6 F + b9 F + b10 F + b12 F + b13 F + b14 F + b17 F + b18 F + b20 F + b22 F + b36 F + b37 F + b38 F + b41 F + b42 F + b45 F + b47 F + b49 F + b50 F + b51 F + b52 F + b55 F + b56 F + b59 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 41))) (e F 5) =
      e F 1 + e F 2 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 41))) (e F 4) =
      e F 0 + e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b4, b5, b6, b9, b10, b12, b13, b14, b17, b18, b20, b22, b36, b37, b38, b41, b42, b45, b47, b49, b50, b51, b52, b55, b56, b59, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_42 : binaryOrbitVector F (binaryIndex 42) =
    b1 F + b2 F + b3 F + b5 F + b6 F + b7 F + b8 F + b9 F + b10 F + b11 F + b51 F + b52 F + b53 F + b54 F + b55 F + b56 F + b59 F + b60 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 42))) (e F 5) =
      e F 0 + e F 1 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 42))) (e F 4) =
      e F 0 + e F 1 + e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b1, b2, b3, b5, b6, b7, b8, b9, b10, b11, b51, b52, b53, b54, b55, b56, b59, b60, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_43 : binaryOrbitVector F (binaryIndex 43) =
    b13 F + b14 F + b15 F + b16 F + b17 F + b18 F + b20 F + b21 F + b22 F + b24 F + b25 F + b26 F + b27 F + b28 F + b29 F + b32 F + b33 F + b34 F + b35 F + b37 F + b38 F + b39 F + b40 F + b41 F + b42 F + b45 F + b46 F + b47 F + b48 F + b49 F + b51 F + b52 F + b53 F + b54 F + b55 F + b56 F + b59 F + b60 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 43))) (e F 5) =
      e F 2 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 43))) (e F 4) =
      e F 0 + e F 1 + e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b13, b14, b15, b16, b17, b18, b20, b21, b22, b24, b25, b26, b27, b28, b29, b32, b33, b34, b35, b37, b38, b39, b40, b41, b42, b45, b46, b47, b48, b49, b51, b52, b53, b54, b55, b56, b59, b60, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_44 : binaryOrbitVector F (binaryIndex 44) =
    b0 F + b1 F + b2 F + b3 F + b23 F + b24 F + b26 F + b27 F + b28 F + b31 F + b32 F + b33 F + b34 F + b50 F + b51 F + b53 F + b54 F + b55 F + b58 F + b59 F + b60 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 44))) (e F 5) =
      e F 0 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 44))) (e F 4) =
      e F 0 + e F 1 + e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b1, b2, b3, b23, b24, b26, b27, b28, b31, b32, b33, b34, b50, b51, b53, b54, b55, b58, b59, b60, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_45 : binaryOrbitVector F (binaryIndex 45) =
    b4 F + b5 F + b7 F + b8 F + b9 F + b10 F + b11 F + b12 F + b13 F + b15 F + b16 F + b17 F + b20 F + b21 F + b22 F + b23 F + b24 F + b26 F + b27 F + b28 F + b31 F + b32 F + b33 F + b34 F + b36 F + b37 F + b39 F + b40 F + b41 F + b44 F + b45 F + b46 F + b47 F + b49 F + b50 F + b51 F + b53 F + b54 F + b55 F + b58 F + b59 F + b60 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 45))) (e F 5) =
      e F 1 + e F 2 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 45))) (e F 4) =
      e F 0 + e F 1 + e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b4, b5, b7, b8, b9, b10, b11, b12, b13, b15, b16, b17, b20, b21, b22, b23, b24, b26, b27, b28, b31, b32, b33, b34, b36, b37, b39, b40, b41, b44, b45, b46, b47, b49, b50, b51, b53, b54, b55, b58, b59, b60, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_46 : binaryOrbitVector F (binaryIndex 46) =
    b1 F + b3 F + b24 F + b28 F + b31 F + b32 F + b34 F + b35 F + b51 F + b55 F + b58 F + b59 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 46))) (e F 5) =
      e F 0 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 46))) (e F 4) =
      e F 0 + e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b1, b3, b24, b28, b31, b32, b34, b35, b51, b55, b58, b59, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_47 : binaryOrbitVector F (binaryIndex 47) =
    b13 F + b17 F + b20 F + b22 F + b37 F + b41 F + b44 F + b45 F + b47 F + b48 F + b49 F + b51 F + b55 F + b58 F + b59 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 47))) (e F 5) =
      e F 2 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 47))) (e F 4) =
      e F 0 + e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (0 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b13, b17, b20, b22, b37, b41, b44, b45, b47, b48, b49, b51, b55, b58, b59, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_48 : binaryOrbitVector F (binaryIndex 48) =
    b4 F + b5 F + b10 F + b12 F + b13 F + b18 F + b19 F + b20 F + b50 F + b51 F + b56 F + b57 F + b59 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 48))) (e F 5) =
      e F 1 + e F 2 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 48))) (e F 4) =
      e F 0 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b4, b5, b10, b12, b13, b18, b19, b20, b50, b51, b56, b57, b59, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_49 : binaryOrbitVector F (binaryIndex 49) =
    b0 F + b1 F + b4 F + b5 F + b10 F + b12 F + b13 F + b18 F + b19 F + b20 F + b36 F + b37 F + b42 F + b43 F + b45 F + b49 F + b50 F + b51 F + b56 F + b57 F + b59 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 49))) (e F 5) =
      e F 0 + e F 1 + e F 2 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 49))) (e F 4) =
      e F 0 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b1, b4, b5, b10, b12, b13, b18, b19, b20, b36, b37, b42, b43, b45, b49, b50, b51, b56, b57, b59, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_50 : binaryOrbitVector F (binaryIndex 50) =
    b8 F + b16 F + b18 F + b19 F + b54 F + b56 F + b57 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 50))) (e F 5) =
      e F 1 + e F 2 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 50))) (e F 4) =
      e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b8, b16, b18, b19, b54, b56, b57, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_51 : binaryOrbitVector F (binaryIndex 51) =
    b8 F + b16 F + b18 F + b19 F + b27 F + b29 F + b30 F + b35 F + b40 F + b42 F + b43 F + b48 F + b49 F + b54 F + b56 F + b57 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 51))) (e F 5) =
      e F 1 + e F 2 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 51))) (e F 4) =
      e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b8, b16, b18, b19, b27, b29, b30, b35, b40, b42, b43, b48, b49, b54, b56, b57, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_52 : binaryOrbitVector F (binaryIndex 52) =
    b1 F + b2 F + b3 F + b5 F + b6 F + b7 F + b8 F + b9 F + b10 F + b11 F + b13 F + b14 F + b15 F + b16 F + b17 F + b18 F + b19 F + b20 F + b21 F + b24 F + b25 F + b26 F + b27 F + b28 F + b29 F + b30 F + b31 F + b32 F + b33 F + b51 F + b52 F + b53 F + b54 F + b55 F + b56 F + b57 F + b58 F + b59 F + b60 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 52))) (e F 5) =
      e F 0 + e F 1 + e F 2 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 52))) (e F 4) =
      e F 0 + e F 1 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b1, b2, b3, b5, b6, b7, b8, b9, b10, b11, b13, b14, b15, b16, b17, b18, b19, b20, b21, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_53 : binaryOrbitVector F (binaryIndex 53) =
    b13 F + b14 F + b15 F + b16 F + b17 F + b18 F + b19 F + b20 F + b21 F + b24 F + b25 F + b26 F + b27 F + b28 F + b29 F + b30 F + b31 F + b32 F + b33 F + b37 F + b38 F + b39 F + b40 F + b41 F + b42 F + b43 F + b44 F + b45 F + b46 F + b49 F + b51 F + b52 F + b53 F + b54 F + b55 F + b56 F + b57 F + b58 F + b59 F + b60 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 53))) (e F 5) =
      e F 2 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 53))) (e F 4) =
      e F 0 + e F 1 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b13, b14, b15, b16, b17, b18, b19, b20, b21, b24, b25, b26, b27, b28, b29, b30, b31, b32, b33, b37, b38, b39, b40, b41, b42, b43, b44, b45, b46, b49, b51, b52, b53, b54, b55, b56, b57, b58, b59, b60, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_54 : binaryOrbitVector F (binaryIndex 54) =
    b0 F + b2 F + b3 F + b4 F + b6 F + b7 F + b9 F + b11 F + b12 F + b14 F + b15 F + b17 F + b18 F + b19 F + b21 F + b23 F + b25 F + b26 F + b28 F + b29 F + b30 F + b31 F + b33 F + b35 F + b50 F + b52 F + b53 F + b55 F + b56 F + b57 F + b58 F + b60 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 54))) (e F 5) =
      e F 0 + e F 1 + e F 2 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 54))) (e F 4) =
      e F 1 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b2, b3, b4, b6, b7, b9, b11, b12, b14, b15, b17, b18, b19, b21, b23, b25, b26, b28, b29, b30, b31, b33, b35, b50, b52, b53, b55, b56, b57, b58, b60, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_55 : binaryOrbitVector F (binaryIndex 55) =
    b0 F + b2 F + b3 F + b12 F + b14 F + b15 F + b17 F + b18 F + b19 F + b21 F + b36 F + b38 F + b39 F + b41 F + b42 F + b43 F + b44 F + b46 F + b48 F + b49 F + b50 F + b52 F + b53 F + b55 F + b56 F + b57 F + b58 F + b60 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 55))) (e F 5) =
      e F 0 + e F 2 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 55))) (e F 4) =
      e F 1 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (0 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b2, b3, b12, b14, b15, b17, b18, b19, b21, b36, b38, b39, b41, b42, b43, b44, b46, b48, b49, b50, b52, b53, b55, b56, b57, b58, b60, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_56 : binaryOrbitVector F (binaryIndex 56) =
    b0 F + b3 F + b4 F + b6 F + b9 F + b10 F + b12 F + b14 F + b17 F + b18 F + b19 F + b20 F + b22 F + b50 F + b52 F + b55 F + b56 F + b57 F + b59 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 56))) (e F 5) =
      e F 0 + e F 1 + e F 2 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 56))) (e F 4) =
      e F 0 + e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b3, b4, b6, b9, b10, b12, b14, b17, b18, b19, b20, b22, b50, b52, b55, b56, b57, b59, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_57 : binaryOrbitVector F (binaryIndex 57) =
    b4 F + b6 F + b9 F + b10 F + b36 F + b38 F + b41 F + b42 F + b43 F + b45 F + b47 F + b49 F + b50 F + b52 F + b55 F + b56 F + b57 F + b59 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 57))) (e F 5) =
      e F 1 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 57))) (e F 4) =
      e F 0 + e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b4, b6, b9, b10, b36, b38, b41, b42, b43, b45, b47, b49, b50, b52, b55, b56, b57, b59, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_58 : binaryOrbitVector F (binaryIndex 58) =
    b0 F + b1 F + b2 F + b3 F + b4 F + b5 F + b7 F + b8 F + b9 F + b11 F + b12 F + b13 F + b15 F + b16 F + b17 F + b18 F + b19 F + b21 F + b22 F + b50 F + b51 F + b53 F + b54 F + b55 F + b56 F + b57 F + b60 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 58))) (e F 5) =
      e F 0 + e F 1 + e F 2 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 58))) (e F 4) =
      e F 1 + e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b1, b2, b3, b4, b5, b7, b8, b9, b11, b12, b13, b15, b16, b17, b18, b19, b21, b22, b50, b51, b53, b54, b55, b56, b57, b60, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_59 : binaryOrbitVector F (binaryIndex 59) =
    b0 F + b1 F + b2 F + b3 F + b23 F + b24 F + b26 F + b27 F + b28 F + b29 F + b30 F + b33 F + b34 F + b35 F + b36 F + b37 F + b39 F + b40 F + b41 F + b42 F + b43 F + b46 F + b47 F + b48 F + b49 F + b50 F + b51 F + b53 F + b54 F + b55 F + b56 F + b57 F + b60 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 59))) (e F 5) =
      e F 0 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 59))) (e F 4) =
      e F 1 + e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (0 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b0, b1, b2, b3, b23, b24, b26, b27, b28, b29, b30, b33, b34, b35, b36, b37, b39, b40, b41, b42, b43, b46, b47, b48, b49, b50, b51, b53, b54, b55, b56, b57, b60, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_60 : binaryOrbitVector F (binaryIndex 60) =
    b13 F + b14 F + b15 F + b16 F + b19 F + b20 F + b21 F + b22 F + b24 F + b25 F + b26 F + b27 F + b30 F + b31 F + b32 F + b33 F + b34 F + b51 F + b52 F + b53 F + b54 F + b57 F + b58 F + b59 F + b60 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 60))) (e F 5) =
      e F 2 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 60))) (e F 4) =
      e F 0 + e F 1 + e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b13, b14, b15, b16, b19, b20, b21, b22, b24, b25, b26, b27, b30, b31, b32, b33, b34, b51, b52, b53, b54, b57, b58, b59, b60, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_61 : binaryOrbitVector F (binaryIndex 61) =
    b1 F + b2 F + b5 F + b6 F + b7 F + b8 F + b10 F + b11 F + b24 F + b25 F + b26 F + b27 F + b30 F + b31 F + b32 F + b33 F + b34 F + b37 F + b38 F + b39 F + b40 F + b43 F + b44 F + b45 F + b46 F + b47 F + b49 F + b51 F + b52 F + b53 F + b54 F + b57 F + b58 F + b59 F + b60 F + b61 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 61))) (e F 5) =
      e F 0 + e F 1 + e F 3 + e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 61))) (e F 4) =
      e F 0 + e F 1 + e F 2 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (0 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b1, b2, b5, b6, b7, b8, b10, b11, b24, b25, b26, b27, b30, b31, b32, b33, b34, b37, b38, b39, b40, b43, b44, b45, b46, b47, b49, b51, b52, b53, b54, b57, b58, b59, b60, b61, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_62 : binaryOrbitVector F (binaryIndex 62) =
    b19 F + b22 F + b30 F + b31 F + b34 F + b35 F + b57 F + b58 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 62))) (e F 5) =
      e F 2 + e F 3 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 62))) (e F 4) =
      e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (0 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b19, b22, b30, b31, b34, b35, b57, b58, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem orbit_63 : binaryOrbitVector F (binaryIndex 63) =
    b43 F + b44 F + b47 F + b48 F + b49 F + b57 F + b58 F + b61 F + b62 F + b63 F := by
  rw [orbit_eq_xy]
  have hx : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 63))) (e F 5) =
      e F 4 + e F 5 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 5) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  have hy : NaturalCoordinates.action F (unipotentProduct (binaryParameters F (binaryIndex 63))) (e F 4) =
      e F 2 + e F 3 + e F 4 := by
    change NaturalCoordinates.action F (rootA (1 : F) * rootB (1 : F) * rootC (1 : F) * rootD (1 : F) * rootE (1 : F) * rootF (1 : F)) (e F 4) = _
    simp only [map_mul, Module.End.mul_apply, map_add, map_smul, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5, rootC_e0, rootC_e1, rootC_e2, rootC_e3, rootC_e4, rootC_e5, rootD_e0, rootD_e1, rootD_e2, rootD_e3, rootD_e4, rootD_e5, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5, rootF_e0, rootF_e1, rootF_e2, rootF_e3, rootF_e4, rootF_e5]
    all_goals simp only [one_pow, zero_pow (by decide : (2 : ℕ) ≠ 0), one_smul, zero_smul, zero_add, add_zero]
    all_goals refine (one_smul F _).symm.trans ?_
    all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]
  rw [hx, hy]
  simp only [b43, b44, b47, b48, b49, b57, b58, b61, b62, b63, pure, TensorProduct.add_tmul, TensorProduct.tmul_add]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

end Atlas.G2.Restricted.Steinberg.OrbitClosure
