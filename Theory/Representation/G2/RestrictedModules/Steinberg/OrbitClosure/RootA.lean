module

public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.Sparse

/-!
# Explicit action on the sparse G₂ tensor generators

The formulas in this file expand the published natural action in the tensor
cube. Each equality is certified by tensor bilinearity and characteristic-two
coefficient arithmetic. Source: the construction for GLS3 2.8.7, 2.8.10(g).
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

theorem rootA_b0 (a : F) : ambientAction F (rootA a) (b0 F) =
    b0 F := by
  simp only [b0, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b1 (a : F) : ambientAction F (rootA a) (b1 F) =
    b1 F := by
  simp only [b1, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b2 (a : F) : ambientAction F (rootA a) (b2 F) =
    b2 F := by
  simp only [b2, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b3 (a : F) : ambientAction F (rootA a) (b3 F) =
    b3 F := by
  simp only [b3, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b4 (a : F) : ambientAction F (rootA a) (b4 F) =
    b4 F := by
  simp only [b4, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b5 (a : F) : ambientAction F (rootA a) (b5 F) =
    b5 F := by
  simp only [b5, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b6 (a : F) : ambientAction F (rootA a) (b6 F) =
    b6 F := by
  simp only [b6, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b7 (a : F) : ambientAction F (rootA a) (b7 F) =
    b7 F := by
  simp only [b7, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b8 (a : F) : ambientAction F (rootA a) (b8 F) =
    b8 F := by
  simp only [b8, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b9 (a : F) : ambientAction F (rootA a) (b9 F) =
    b9 F := by
  simp only [b9, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b10 (a : F) : ambientAction F (rootA a) (b10 F) =
    b10 F := by
  simp only [b10, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b11 (a : F) : ambientAction F (rootA a) (b11 F) =
    b11 F := by
  simp only [b11, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b12 (a : F) : ambientAction F (rootA a) (b12 F) =
    b12 F := by
  simp only [b12, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b13 (a : F) : ambientAction F (rootA a) (b13 F) =
    b13 F := by
  simp only [b13, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b14 (a : F) : ambientAction F (rootA a) (b14 F) =
    b14 F := by
  simp only [b14, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b15 (a : F) : ambientAction F (rootA a) (b15 F) =
    b15 F + a • b0 F := by
  simp only [b0, b15, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b16 (a : F) : ambientAction F (rootA a) (b16 F) =
    b16 F + a • b4 F := by
  simp only [b4, b16, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b17 (a : F) : ambientAction F (rootA a) (b17 F) =
    b17 F + a • b1 F := by
  simp only [b1, b17, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b18 (a : F) : ambientAction F (rootA a) (b18 F) =
    b18 F + a • b5 F + a • b12 F := by
  simp only [b5, b12, b18, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b19 (a : F) : ambientAction F (rootA a) (b19 F) =
    b19 F + a • b13 F := by
  simp only [b13, b19, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b20 (a : F) : ambientAction F (rootA a) (b20 F) =
    b20 F + a • b12 F := by
  simp only [b12, b20, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b21 (a : F) : ambientAction F (rootA a) (b21 F) =
    b21 F + a • b6 F := by
  simp only [b6, b21, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b22 (a : F) : ambientAction F (rootA a) (b22 F) =
    b22 F + a • b14 F := by
  simp only [b14, b22, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b23 (a : F) : ambientAction F (rootA a) (b23 F) =
    b23 F := by
  simp only [b23, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b24 (a : F) : ambientAction F (rootA a) (b24 F) =
    b24 F + a • b0 F := by
  simp only [b0, b24, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b25 (a : F) : ambientAction F (rootA a) (b25 F) =
    b25 F + a • b4 F := by
  simp only [b4, b25, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b26 (a : F) : ambientAction F (rootA a) (b26 F) =
    b26 F := by
  simp only [b26, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b27 (a : F) : ambientAction F (rootA a) (b27 F) =
    b27 F := by
  simp only [b27, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b28 (a : F) : ambientAction F (rootA a) (b28 F) =
    b28 F + a • b2 F := by
  simp only [b2, b28, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b29 (a : F) : ambientAction F (rootA a) (b29 F) =
    b29 F + a • b7 F + a • b23 F := by
  simp only [b7, b23, b29, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b30 (a : F) : ambientAction F (rootA a) (b30 F) =
    b30 F + a • b15 F + a • b24 F := by
  simp only [b15, b24, b30, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b31 (a : F) : ambientAction F (rootA a) (b31 F) =
    b31 F + a • b26 F := by
  simp only [b26, b31, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b32 (a : F) : ambientAction F (rootA a) (b32 F) =
    b32 F + a • b23 F := by
  simp only [b23, b32, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b33 (a : F) : ambientAction F (rootA a) (b33 F) =
    b33 F + a • b8 F := by
  simp only [b8, b33, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b34 (a : F) : ambientAction F (rootA a) (b34 F) =
    b34 F + a • b16 F + a • b25 F := by
  simp only [b16, b25, b34, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b35 (a : F) : ambientAction F (rootA a) (b35 F) =
    b35 F + a • b27 F := by
  simp only [b27, b35, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b36 (a : F) : ambientAction F (rootA a) (b36 F) =
    b36 F + a • b0 F := by
  simp only [b0, b36, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b37 (a : F) : ambientAction F (rootA a) (b37 F) =
    b37 F := by
  simp only [b37, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b38 (a : F) : ambientAction F (rootA a) (b38 F) =
    b38 F + a • b5 F := by
  simp only [b5, b38, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b39 (a : F) : ambientAction F (rootA a) (b39 F) =
    b39 F := by
  simp only [b39, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b40 (a : F) : ambientAction F (rootA a) (b40 F) =
    b40 F + a • b7 F := by
  simp only [b7, b40, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b41 (a : F) : ambientAction F (rootA a) (b41 F) =
    b41 F + a • b3 F := by
  simp only [b3, b41, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b42 (a : F) : ambientAction F (rootA a) (b42 F) =
    b42 F + a • b15 F + a • b36 F + a^2 • b0 F := by
  simp only [b0, b15, b36, b42, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b43 (a : F) : ambientAction F (rootA a) (b43 F) =
    b43 F + a • b37 F + a^2 • b1 F := by
  simp only [b1, b37, b43, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b44 (a : F) : ambientAction F (rootA a) (b44 F) =
    b44 F + a • b39 F + a^2 • b2 F := by
  simp only [b2, b39, b44, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b45 (a : F) : ambientAction F (rootA a) (b45 F) =
    b45 F + a • b15 F + a • b36 F := by
  simp only [b15, b36, b45, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b46 (a : F) : ambientAction F (rootA a) (b46 F) =
    b46 F + a • b10 F + a^2 • b4 F := by
  simp only [b4, b10, b46, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b47 (a : F) : ambientAction F (rootA a) (b47 F) =
    b47 F + a • b18 F + a • b20 F + a • b38 F + a^2 • b12 F := by
  simp only [b12, b18, b20, b38, b47, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b48 (a : F) : ambientAction F (rootA a) (b48 F) =
    b48 F + a • b29 F + a • b32 F + a • b40 F + a^2 • b23 F := by
  simp only [b23, b29, b32, b40, b48, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b49 (a : F) : ambientAction F (rootA a) (b49 F) =
    b49 F + a • b42 F + a • b45 F + a^2 • b36 F + a^3 • b0 F := by
  simp only [b0, b36, b42, b45, b49, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b50 (a : F) : ambientAction F (rootA a) (b50 F) =
    b50 F + a • b4 F := by
  simp only [b4, b50, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b51 (a : F) : ambientAction F (rootA a) (b51 F) =
    b51 F + a • b5 F := by
  simp only [b5, b51, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b52 (a : F) : ambientAction F (rootA a) (b52 F) =
    b52 F := by
  simp only [b52, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b53 (a : F) : ambientAction F (rootA a) (b53 F) =
    b53 F + a • b7 F := by
  simp only [b7, b53, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b54 (a : F) : ambientAction F (rootA a) (b54 F) =
    b54 F := by
  simp only [b54, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b55 (a : F) : ambientAction F (rootA a) (b55 F) =
    b55 F + a • b9 F + a^2 • b0 F := by
  simp only [b0, b9, b55, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b56 (a : F) : ambientAction F (rootA a) (b56 F) =
    b56 F + a • b10 F + a • b16 F + a • b50 F := by
  simp only [b10, b16, b50, b56, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b57 (a : F) : ambientAction F (rootA a) (b57 F) =
    b57 F + a • b18 F + a • b20 F + a • b51 F + a^2 • b5 F + a^2 • b12 F := by
  simp only [b5, b12, b18, b20, b51, b57, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b58 (a : F) : ambientAction F (rootA a) (b58 F) =
    b58 F + a • b29 F + a • b32 F + a • b53 F + a^2 • b7 F + a^2 • b23 F := by
  simp only [b7, b23, b29, b32, b53, b58, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b59 (a : F) : ambientAction F (rootA a) (b59 F) =
    b59 F + a • b10 F + a • b16 F + a • b50 F + a^2 • b4 F := by
  simp only [b4, b10, b16, b50, b59, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b60 (a : F) : ambientAction F (rootA a) (b60 F) =
    b60 F + a • b11 F := by
  simp only [b11, b60, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b61 (a : F) : ambientAction F (rootA a) (b61 F) =
    b61 F + a • b52 F + a^2 • b6 F := by
  simp only [b6, b52, b61, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b62 (a : F) : ambientAction F (rootA a) (b62 F) =
    b62 F + a • b54 F + a^2 • b8 F := by
  simp only [b8, b54, b62, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootA_b63 (a : F) : ambientAction F (rootA a) (b63 F) =
    b63 F + a • b56 F + a • b59 F + a^2 • b10 F + a^2 • b50 F + a^3 • b4 F := by
  simp only [b4, b10, b50, b56, b59, b63, map_add, ambientAction_pure, rootA_e0, rootA_e1, rootA_e2, rootA_e3, rootA_e4, rootA_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

/-- Preservation by the actual rootA elements, at every parameter. -/
theorem rootA_preserves (a : F) :
    ∀ v ∈ sparseSpan F, ambientAction F (rootA a) v ∈ sparseSpan F := by
  apply preserves_of_generators
  intro i
  fin_cases i
  · change ambientAction F (rootA a) (b0 F) ∈ sparseSpan F
    rw [rootA_b0]
    exact (generator_mem F 0)
  · change ambientAction F (rootA a) (b1 F) ∈ sparseSpan F
    rw [rootA_b1]
    exact (generator_mem F 1)
  · change ambientAction F (rootA a) (b2 F) ∈ sparseSpan F
    rw [rootA_b2]
    exact (generator_mem F 2)
  · change ambientAction F (rootA a) (b3 F) ∈ sparseSpan F
    rw [rootA_b3]
    exact (generator_mem F 3)
  · change ambientAction F (rootA a) (b4 F) ∈ sparseSpan F
    rw [rootA_b4]
    exact (generator_mem F 4)
  · change ambientAction F (rootA a) (b5 F) ∈ sparseSpan F
    rw [rootA_b5]
    exact (generator_mem F 5)
  · change ambientAction F (rootA a) (b6 F) ∈ sparseSpan F
    rw [rootA_b6]
    exact (generator_mem F 6)
  · change ambientAction F (rootA a) (b7 F) ∈ sparseSpan F
    rw [rootA_b7]
    exact (generator_mem F 7)
  · change ambientAction F (rootA a) (b8 F) ∈ sparseSpan F
    rw [rootA_b8]
    exact (generator_mem F 8)
  · change ambientAction F (rootA a) (b9 F) ∈ sparseSpan F
    rw [rootA_b9]
    exact (generator_mem F 9)
  · change ambientAction F (rootA a) (b10 F) ∈ sparseSpan F
    rw [rootA_b10]
    exact (generator_mem F 10)
  · change ambientAction F (rootA a) (b11 F) ∈ sparseSpan F
    rw [rootA_b11]
    exact (generator_mem F 11)
  · change ambientAction F (rootA a) (b12 F) ∈ sparseSpan F
    rw [rootA_b12]
    exact (generator_mem F 12)
  · change ambientAction F (rootA a) (b13 F) ∈ sparseSpan F
    rw [rootA_b13]
    exact (generator_mem F 13)
  · change ambientAction F (rootA a) (b14 F) ∈ sparseSpan F
    rw [rootA_b14]
    exact (generator_mem F 14)
  · change ambientAction F (rootA a) (b15 F) ∈ sparseSpan F
    rw [rootA_b15]
    exact ((sparseSpan F).add_mem (generator_mem F 15) ((sparseSpan F).smul_mem a (generator_mem F 0)))
  · change ambientAction F (rootA a) (b16 F) ∈ sparseSpan F
    rw [rootA_b16]
    exact ((sparseSpan F).add_mem (generator_mem F 16) ((sparseSpan F).smul_mem a (generator_mem F 4)))
  · change ambientAction F (rootA a) (b17 F) ∈ sparseSpan F
    rw [rootA_b17]
    exact ((sparseSpan F).add_mem (generator_mem F 17) ((sparseSpan F).smul_mem a (generator_mem F 1)))
  · change ambientAction F (rootA a) (b18 F) ∈ sparseSpan F
    rw [rootA_b18]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 18) ((sparseSpan F).smul_mem a (generator_mem F 5))) ((sparseSpan F).smul_mem a (generator_mem F 12)))
  · change ambientAction F (rootA a) (b19 F) ∈ sparseSpan F
    rw [rootA_b19]
    exact ((sparseSpan F).add_mem (generator_mem F 19) ((sparseSpan F).smul_mem a (generator_mem F 13)))
  · change ambientAction F (rootA a) (b20 F) ∈ sparseSpan F
    rw [rootA_b20]
    exact ((sparseSpan F).add_mem (generator_mem F 20) ((sparseSpan F).smul_mem a (generator_mem F 12)))
  · change ambientAction F (rootA a) (b21 F) ∈ sparseSpan F
    rw [rootA_b21]
    exact ((sparseSpan F).add_mem (generator_mem F 21) ((sparseSpan F).smul_mem a (generator_mem F 6)))
  · change ambientAction F (rootA a) (b22 F) ∈ sparseSpan F
    rw [rootA_b22]
    exact ((sparseSpan F).add_mem (generator_mem F 22) ((sparseSpan F).smul_mem a (generator_mem F 14)))
  · change ambientAction F (rootA a) (b23 F) ∈ sparseSpan F
    rw [rootA_b23]
    exact (generator_mem F 23)
  · change ambientAction F (rootA a) (b24 F) ∈ sparseSpan F
    rw [rootA_b24]
    exact ((sparseSpan F).add_mem (generator_mem F 24) ((sparseSpan F).smul_mem a (generator_mem F 0)))
  · change ambientAction F (rootA a) (b25 F) ∈ sparseSpan F
    rw [rootA_b25]
    exact ((sparseSpan F).add_mem (generator_mem F 25) ((sparseSpan F).smul_mem a (generator_mem F 4)))
  · change ambientAction F (rootA a) (b26 F) ∈ sparseSpan F
    rw [rootA_b26]
    exact (generator_mem F 26)
  · change ambientAction F (rootA a) (b27 F) ∈ sparseSpan F
    rw [rootA_b27]
    exact (generator_mem F 27)
  · change ambientAction F (rootA a) (b28 F) ∈ sparseSpan F
    rw [rootA_b28]
    exact ((sparseSpan F).add_mem (generator_mem F 28) ((sparseSpan F).smul_mem a (generator_mem F 2)))
  · change ambientAction F (rootA a) (b29 F) ∈ sparseSpan F
    rw [rootA_b29]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 29) ((sparseSpan F).smul_mem a (generator_mem F 7))) ((sparseSpan F).smul_mem a (generator_mem F 23)))
  · change ambientAction F (rootA a) (b30 F) ∈ sparseSpan F
    rw [rootA_b30]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 30) ((sparseSpan F).smul_mem a (generator_mem F 15))) ((sparseSpan F).smul_mem a (generator_mem F 24)))
  · change ambientAction F (rootA a) (b31 F) ∈ sparseSpan F
    rw [rootA_b31]
    exact ((sparseSpan F).add_mem (generator_mem F 31) ((sparseSpan F).smul_mem a (generator_mem F 26)))
  · change ambientAction F (rootA a) (b32 F) ∈ sparseSpan F
    rw [rootA_b32]
    exact ((sparseSpan F).add_mem (generator_mem F 32) ((sparseSpan F).smul_mem a (generator_mem F 23)))
  · change ambientAction F (rootA a) (b33 F) ∈ sparseSpan F
    rw [rootA_b33]
    exact ((sparseSpan F).add_mem (generator_mem F 33) ((sparseSpan F).smul_mem a (generator_mem F 8)))
  · change ambientAction F (rootA a) (b34 F) ∈ sparseSpan F
    rw [rootA_b34]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 34) ((sparseSpan F).smul_mem a (generator_mem F 16))) ((sparseSpan F).smul_mem a (generator_mem F 25)))
  · change ambientAction F (rootA a) (b35 F) ∈ sparseSpan F
    rw [rootA_b35]
    exact ((sparseSpan F).add_mem (generator_mem F 35) ((sparseSpan F).smul_mem a (generator_mem F 27)))
  · change ambientAction F (rootA a) (b36 F) ∈ sparseSpan F
    rw [rootA_b36]
    exact ((sparseSpan F).add_mem (generator_mem F 36) ((sparseSpan F).smul_mem a (generator_mem F 0)))
  · change ambientAction F (rootA a) (b37 F) ∈ sparseSpan F
    rw [rootA_b37]
    exact (generator_mem F 37)
  · change ambientAction F (rootA a) (b38 F) ∈ sparseSpan F
    rw [rootA_b38]
    exact ((sparseSpan F).add_mem (generator_mem F 38) ((sparseSpan F).smul_mem a (generator_mem F 5)))
  · change ambientAction F (rootA a) (b39 F) ∈ sparseSpan F
    rw [rootA_b39]
    exact (generator_mem F 39)
  · change ambientAction F (rootA a) (b40 F) ∈ sparseSpan F
    rw [rootA_b40]
    exact ((sparseSpan F).add_mem (generator_mem F 40) ((sparseSpan F).smul_mem a (generator_mem F 7)))
  · change ambientAction F (rootA a) (b41 F) ∈ sparseSpan F
    rw [rootA_b41]
    exact ((sparseSpan F).add_mem (generator_mem F 41) ((sparseSpan F).smul_mem a (generator_mem F 3)))
  · change ambientAction F (rootA a) (b42 F) ∈ sparseSpan F
    rw [rootA_b42]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 42) ((sparseSpan F).smul_mem a (generator_mem F 15))) ((sparseSpan F).smul_mem a (generator_mem F 36))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 0)))
  · change ambientAction F (rootA a) (b43 F) ∈ sparseSpan F
    rw [rootA_b43]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 43) ((sparseSpan F).smul_mem a (generator_mem F 37))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 1)))
  · change ambientAction F (rootA a) (b44 F) ∈ sparseSpan F
    rw [rootA_b44]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 44) ((sparseSpan F).smul_mem a (generator_mem F 39))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 2)))
  · change ambientAction F (rootA a) (b45 F) ∈ sparseSpan F
    rw [rootA_b45]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 45) ((sparseSpan F).smul_mem a (generator_mem F 15))) ((sparseSpan F).smul_mem a (generator_mem F 36)))
  · change ambientAction F (rootA a) (b46 F) ∈ sparseSpan F
    rw [rootA_b46]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 46) ((sparseSpan F).smul_mem a (generator_mem F 10))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 4)))
  · change ambientAction F (rootA a) (b47 F) ∈ sparseSpan F
    rw [rootA_b47]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 47) ((sparseSpan F).smul_mem a (generator_mem F 18))) ((sparseSpan F).smul_mem a (generator_mem F 20))) ((sparseSpan F).smul_mem a (generator_mem F 38))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 12)))
  · change ambientAction F (rootA a) (b48 F) ∈ sparseSpan F
    rw [rootA_b48]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 48) ((sparseSpan F).smul_mem a (generator_mem F 29))) ((sparseSpan F).smul_mem a (generator_mem F 32))) ((sparseSpan F).smul_mem a (generator_mem F 40))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 23)))
  · change ambientAction F (rootA a) (b49 F) ∈ sparseSpan F
    rw [rootA_b49]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 49) ((sparseSpan F).smul_mem a (generator_mem F 42))) ((sparseSpan F).smul_mem a (generator_mem F 45))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 36))) ((sparseSpan F).smul_mem (a^3) (generator_mem F 0)))
  · change ambientAction F (rootA a) (b50 F) ∈ sparseSpan F
    rw [rootA_b50]
    exact ((sparseSpan F).add_mem (generator_mem F 50) ((sparseSpan F).smul_mem a (generator_mem F 4)))
  · change ambientAction F (rootA a) (b51 F) ∈ sparseSpan F
    rw [rootA_b51]
    exact ((sparseSpan F).add_mem (generator_mem F 51) ((sparseSpan F).smul_mem a (generator_mem F 5)))
  · change ambientAction F (rootA a) (b52 F) ∈ sparseSpan F
    rw [rootA_b52]
    exact (generator_mem F 52)
  · change ambientAction F (rootA a) (b53 F) ∈ sparseSpan F
    rw [rootA_b53]
    exact ((sparseSpan F).add_mem (generator_mem F 53) ((sparseSpan F).smul_mem a (generator_mem F 7)))
  · change ambientAction F (rootA a) (b54 F) ∈ sparseSpan F
    rw [rootA_b54]
    exact (generator_mem F 54)
  · change ambientAction F (rootA a) (b55 F) ∈ sparseSpan F
    rw [rootA_b55]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 55) ((sparseSpan F).smul_mem a (generator_mem F 9))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 0)))
  · change ambientAction F (rootA a) (b56 F) ∈ sparseSpan F
    rw [rootA_b56]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 56) ((sparseSpan F).smul_mem a (generator_mem F 10))) ((sparseSpan F).smul_mem a (generator_mem F 16))) ((sparseSpan F).smul_mem a (generator_mem F 50)))
  · change ambientAction F (rootA a) (b57 F) ∈ sparseSpan F
    rw [rootA_b57]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 57) ((sparseSpan F).smul_mem a (generator_mem F 18))) ((sparseSpan F).smul_mem a (generator_mem F 20))) ((sparseSpan F).smul_mem a (generator_mem F 51))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 5))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 12)))
  · change ambientAction F (rootA a) (b58 F) ∈ sparseSpan F
    rw [rootA_b58]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 58) ((sparseSpan F).smul_mem a (generator_mem F 29))) ((sparseSpan F).smul_mem a (generator_mem F 32))) ((sparseSpan F).smul_mem a (generator_mem F 53))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 7))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 23)))
  · change ambientAction F (rootA a) (b59 F) ∈ sparseSpan F
    rw [rootA_b59]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 59) ((sparseSpan F).smul_mem a (generator_mem F 10))) ((sparseSpan F).smul_mem a (generator_mem F 16))) ((sparseSpan F).smul_mem a (generator_mem F 50))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 4)))
  · change ambientAction F (rootA a) (b60 F) ∈ sparseSpan F
    rw [rootA_b60]
    exact ((sparseSpan F).add_mem (generator_mem F 60) ((sparseSpan F).smul_mem a (generator_mem F 11)))
  · change ambientAction F (rootA a) (b61 F) ∈ sparseSpan F
    rw [rootA_b61]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 61) ((sparseSpan F).smul_mem a (generator_mem F 52))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 6)))
  · change ambientAction F (rootA a) (b62 F) ∈ sparseSpan F
    rw [rootA_b62]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 62) ((sparseSpan F).smul_mem a (generator_mem F 54))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 8)))
  · change ambientAction F (rootA a) (b63 F) ∈ sparseSpan F
    rw [rootA_b63]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 63) ((sparseSpan F).smul_mem a (generator_mem F 56))) ((sparseSpan F).smul_mem a (generator_mem F 59))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 10))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 50))) ((sparseSpan F).smul_mem (a^3) (generator_mem F 4)))

end Atlas.G2.Restricted.Steinberg.OrbitClosure
