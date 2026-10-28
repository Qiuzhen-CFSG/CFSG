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

theorem rootB_b0 (a : F) : ambientAction F (rootB a) (b0 F) =
    b0 F := by
  simp only [b0, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b1 (a : F) : ambientAction F (rootB a) (b1 F) =
    b1 F := by
  simp only [b1, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b2 (a : F) : ambientAction F (rootB a) (b2 F) =
    b2 F := by
  simp only [b2, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b3 (a : F) : ambientAction F (rootB a) (b3 F) =
    b3 F := by
  simp only [b3, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b4 (a : F) : ambientAction F (rootB a) (b4 F) =
    b4 F := by
  simp only [b4, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b5 (a : F) : ambientAction F (rootB a) (b5 F) =
    b5 F := by
  simp only [b5, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b6 (a : F) : ambientAction F (rootB a) (b6 F) =
    b6 F := by
  simp only [b6, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b7 (a : F) : ambientAction F (rootB a) (b7 F) =
    b7 F + a • b0 F := by
  simp only [b0, b7, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b8 (a : F) : ambientAction F (rootB a) (b8 F) =
    b8 F + a • b4 F := by
  simp only [b4, b8, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b9 (a : F) : ambientAction F (rootB a) (b9 F) =
    b9 F + a • b1 F := by
  simp only [b1, b9, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b10 (a : F) : ambientAction F (rootB a) (b10 F) =
    b10 F + a • b5 F := by
  simp only [b5, b10, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b11 (a : F) : ambientAction F (rootB a) (b11 F) =
    b11 F + a • b6 F := by
  simp only [b6, b11, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b12 (a : F) : ambientAction F (rootB a) (b12 F) =
    b12 F := by
  simp only [b12, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b13 (a : F) : ambientAction F (rootB a) (b13 F) =
    b13 F := by
  simp only [b13, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b14 (a : F) : ambientAction F (rootB a) (b14 F) =
    b14 F := by
  simp only [b14, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b15 (a : F) : ambientAction F (rootB a) (b15 F) =
    b15 F := by
  simp only [b15, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b16 (a : F) : ambientAction F (rootB a) (b16 F) =
    b16 F + a • b5 F + a • b12 F := by
  simp only [b5, b12, b16, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b17 (a : F) : ambientAction F (rootB a) (b17 F) =
    b17 F := by
  simp only [b17, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b18 (a : F) : ambientAction F (rootB a) (b18 F) =
    b18 F + a • b13 F := by
  simp only [b13, b18, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b19 (a : F) : ambientAction F (rootB a) (b19 F) =
    b19 F := by
  simp only [b19, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b20 (a : F) : ambientAction F (rootB a) (b20 F) =
    b20 F := by
  simp only [b20, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b21 (a : F) : ambientAction F (rootB a) (b21 F) =
    b21 F + a • b14 F := by
  simp only [b14, b21, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b22 (a : F) : ambientAction F (rootB a) (b22 F) =
    b22 F := by
  simp only [b22, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b23 (a : F) : ambientAction F (rootB a) (b23 F) =
    b23 F := by
  simp only [b23, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b24 (a : F) : ambientAction F (rootB a) (b24 F) =
    b24 F + a • b1 F := by
  simp only [b1, b24, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b25 (a : F) : ambientAction F (rootB a) (b25 F) =
    b25 F + a • b5 F := by
  simp only [b5, b25, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b26 (a : F) : ambientAction F (rootB a) (b26 F) =
    b26 F + a • b2 F := by
  simp only [b2, b26, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b27 (a : F) : ambientAction F (rootB a) (b27 F) =
    b27 F + a • b23 F + a^2 • b0 F := by
  simp only [b0, b23, b27, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b28 (a : F) : ambientAction F (rootB a) (b28 F) =
    b28 F := by
  simp only [b28, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b29 (a : F) : ambientAction F (rootB a) (b29 F) =
    b29 F + a • b9 F + a • b24 F + a^2 • b1 F := by
  simp only [b1, b9, b24, b29, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b30 (a : F) : ambientAction F (rootB a) (b30 F) =
    b30 F + a • b17 F := by
  simp only [b17, b30, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b31 (a : F) : ambientAction F (rootB a) (b31 F) =
    b31 F + a • b28 F + a^2 • b3 F := by
  simp only [b3, b28, b31, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b32 (a : F) : ambientAction F (rootB a) (b32 F) =
    b32 F + a^2 • b1 F := by
  simp only [b1, b32, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b33 (a : F) : ambientAction F (rootB a) (b33 F) =
    b33 F + a • b10 F + a • b25 F + a^2 • b5 F := by
  simp only [b5, b10, b25, b33, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b34 (a : F) : ambientAction F (rootB a) (b34 F) =
    b34 F + a • b20 F + a^2 • b13 F := by
  simp only [b13, b20, b34, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b35 (a : F) : ambientAction F (rootB a) (b35 F) =
    b35 F + a • b32 F + a^2 • b24 F + a^3 • b1 F := by
  simp only [b1, b24, b32, b35, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b36 (a : F) : ambientAction F (rootB a) (b36 F) =
    b36 F + a • b1 F := by
  simp only [b1, b36, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b37 (a : F) : ambientAction F (rootB a) (b37 F) =
    b37 F := by
  simp only [b37, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b38 (a : F) : ambientAction F (rootB a) (b38 F) =
    b38 F := by
  simp only [b38, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b39 (a : F) : ambientAction F (rootB a) (b39 F) =
    b39 F + a • b3 F := by
  simp only [b3, b39, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b40 (a : F) : ambientAction F (rootB a) (b40 F) =
    b40 F + a • b9 F + a • b36 F := by
  simp only [b9, b36, b40, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b41 (a : F) : ambientAction F (rootB a) (b41 F) =
    b41 F := by
  simp only [b41, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b42 (a : F) : ambientAction F (rootB a) (b42 F) =
    b42 F + a • b17 F + a • b37 F := by
  simp only [b17, b37, b42, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b43 (a : F) : ambientAction F (rootB a) (b43 F) =
    b43 F := by
  simp only [b43, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b44 (a : F) : ambientAction F (rootB a) (b44 F) =
    b44 F + a • b41 F := by
  simp only [b41, b44, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b45 (a : F) : ambientAction F (rootB a) (b45 F) =
    b45 F + a • b17 F := by
  simp only [b17, b45, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b46 (a : F) : ambientAction F (rootB a) (b46 F) =
    b46 F + a • b38 F := by
  simp only [b38, b46, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b47 (a : F) : ambientAction F (rootB a) (b47 F) =
    b47 F + a • b19 F := by
  simp only [b19, b47, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b48 (a : F) : ambientAction F (rootB a) (b48 F) =
    b48 F + a • b30 F + a • b45 F + a^2 • b37 F := by
  simp only [b30, b37, b45, b48, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b49 (a : F) : ambientAction F (rootB a) (b49 F) =
    b49 F + a • b43 F := by
  simp only [b43, b49, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b50 (a : F) : ambientAction F (rootB a) (b50 F) =
    b50 F + a • b12 F := by
  simp only [b12, b50, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b51 (a : F) : ambientAction F (rootB a) (b51 F) =
    b51 F + a • b13 F := by
  simp only [b13, b51, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b52 (a : F) : ambientAction F (rootB a) (b52 F) =
    b52 F + a • b14 F := by
  simp only [b14, b52, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b53 (a : F) : ambientAction F (rootB a) (b53 F) =
    b53 F + a • b15 F + a^2 • b1 F := by
  simp only [b1, b15, b53, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b54 (a : F) : ambientAction F (rootB a) (b54 F) =
    b54 F + a • b10 F + a • b16 F + a • b50 F + a^2 • b5 F + a^2 • b12 F := by
  simp only [b5, b10, b12, b16, b50, b54, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b55 (a : F) : ambientAction F (rootB a) (b55 F) =
    b55 F + a • b17 F := by
  simp only [b17, b55, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b56 (a : F) : ambientAction F (rootB a) (b56 F) =
    b56 F + a • b18 F + a • b20 F + a • b51 F := by
  simp only [b18, b20, b51, b56, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b57 (a : F) : ambientAction F (rootB a) (b57 F) =
    b57 F := by
  simp only [b57, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b58 (a : F) : ambientAction F (rootB a) (b58 F) =
    b58 F + a • b30 F + a • b55 F + a^2 • b17 F := by
  simp only [b17, b30, b55, b58, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b59 (a : F) : ambientAction F (rootB a) (b59 F) =
    b59 F + a^2 • b13 F := by
  simp only [b13, b59, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b60 (a : F) : ambientAction F (rootB a) (b60 F) =
    b60 F + a • b21 F + a • b52 F + a^2 • b14 F := by
  simp only [b14, b21, b52, b60, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b61 (a : F) : ambientAction F (rootB a) (b61 F) =
    b61 F + a • b22 F := by
  simp only [b22, b61, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b62 (a : F) : ambientAction F (rootB a) (b62 F) =
    b62 F + a • b59 F + a^2 • b20 F + a^2 • b51 F + a^3 • b13 F := by
  simp only [b13, b20, b51, b59, b62, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootB_b63 (a : F) : ambientAction F (rootB a) (b63 F) =
    b63 F + a • b57 F + a^2 • b19 F := by
  simp only [b19, b57, b63, map_add, ambientAction_pure, rootB_e0, rootB_e1, rootB_e2, rootB_e3, rootB_e4, rootB_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

/-- Preservation by the actual rootB elements, at every parameter. -/
theorem rootB_preserves (a : F) :
    ∀ v ∈ sparseSpan F, ambientAction F (rootB a) v ∈ sparseSpan F := by
  apply preserves_of_generators
  intro i
  fin_cases i
  · change ambientAction F (rootB a) (b0 F) ∈ sparseSpan F
    rw [rootB_b0]
    exact (generator_mem F 0)
  · change ambientAction F (rootB a) (b1 F) ∈ sparseSpan F
    rw [rootB_b1]
    exact (generator_mem F 1)
  · change ambientAction F (rootB a) (b2 F) ∈ sparseSpan F
    rw [rootB_b2]
    exact (generator_mem F 2)
  · change ambientAction F (rootB a) (b3 F) ∈ sparseSpan F
    rw [rootB_b3]
    exact (generator_mem F 3)
  · change ambientAction F (rootB a) (b4 F) ∈ sparseSpan F
    rw [rootB_b4]
    exact (generator_mem F 4)
  · change ambientAction F (rootB a) (b5 F) ∈ sparseSpan F
    rw [rootB_b5]
    exact (generator_mem F 5)
  · change ambientAction F (rootB a) (b6 F) ∈ sparseSpan F
    rw [rootB_b6]
    exact (generator_mem F 6)
  · change ambientAction F (rootB a) (b7 F) ∈ sparseSpan F
    rw [rootB_b7]
    exact ((sparseSpan F).add_mem (generator_mem F 7) ((sparseSpan F).smul_mem a (generator_mem F 0)))
  · change ambientAction F (rootB a) (b8 F) ∈ sparseSpan F
    rw [rootB_b8]
    exact ((sparseSpan F).add_mem (generator_mem F 8) ((sparseSpan F).smul_mem a (generator_mem F 4)))
  · change ambientAction F (rootB a) (b9 F) ∈ sparseSpan F
    rw [rootB_b9]
    exact ((sparseSpan F).add_mem (generator_mem F 9) ((sparseSpan F).smul_mem a (generator_mem F 1)))
  · change ambientAction F (rootB a) (b10 F) ∈ sparseSpan F
    rw [rootB_b10]
    exact ((sparseSpan F).add_mem (generator_mem F 10) ((sparseSpan F).smul_mem a (generator_mem F 5)))
  · change ambientAction F (rootB a) (b11 F) ∈ sparseSpan F
    rw [rootB_b11]
    exact ((sparseSpan F).add_mem (generator_mem F 11) ((sparseSpan F).smul_mem a (generator_mem F 6)))
  · change ambientAction F (rootB a) (b12 F) ∈ sparseSpan F
    rw [rootB_b12]
    exact (generator_mem F 12)
  · change ambientAction F (rootB a) (b13 F) ∈ sparseSpan F
    rw [rootB_b13]
    exact (generator_mem F 13)
  · change ambientAction F (rootB a) (b14 F) ∈ sparseSpan F
    rw [rootB_b14]
    exact (generator_mem F 14)
  · change ambientAction F (rootB a) (b15 F) ∈ sparseSpan F
    rw [rootB_b15]
    exact (generator_mem F 15)
  · change ambientAction F (rootB a) (b16 F) ∈ sparseSpan F
    rw [rootB_b16]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 16) ((sparseSpan F).smul_mem a (generator_mem F 5))) ((sparseSpan F).smul_mem a (generator_mem F 12)))
  · change ambientAction F (rootB a) (b17 F) ∈ sparseSpan F
    rw [rootB_b17]
    exact (generator_mem F 17)
  · change ambientAction F (rootB a) (b18 F) ∈ sparseSpan F
    rw [rootB_b18]
    exact ((sparseSpan F).add_mem (generator_mem F 18) ((sparseSpan F).smul_mem a (generator_mem F 13)))
  · change ambientAction F (rootB a) (b19 F) ∈ sparseSpan F
    rw [rootB_b19]
    exact (generator_mem F 19)
  · change ambientAction F (rootB a) (b20 F) ∈ sparseSpan F
    rw [rootB_b20]
    exact (generator_mem F 20)
  · change ambientAction F (rootB a) (b21 F) ∈ sparseSpan F
    rw [rootB_b21]
    exact ((sparseSpan F).add_mem (generator_mem F 21) ((sparseSpan F).smul_mem a (generator_mem F 14)))
  · change ambientAction F (rootB a) (b22 F) ∈ sparseSpan F
    rw [rootB_b22]
    exact (generator_mem F 22)
  · change ambientAction F (rootB a) (b23 F) ∈ sparseSpan F
    rw [rootB_b23]
    exact (generator_mem F 23)
  · change ambientAction F (rootB a) (b24 F) ∈ sparseSpan F
    rw [rootB_b24]
    exact ((sparseSpan F).add_mem (generator_mem F 24) ((sparseSpan F).smul_mem a (generator_mem F 1)))
  · change ambientAction F (rootB a) (b25 F) ∈ sparseSpan F
    rw [rootB_b25]
    exact ((sparseSpan F).add_mem (generator_mem F 25) ((sparseSpan F).smul_mem a (generator_mem F 5)))
  · change ambientAction F (rootB a) (b26 F) ∈ sparseSpan F
    rw [rootB_b26]
    exact ((sparseSpan F).add_mem (generator_mem F 26) ((sparseSpan F).smul_mem a (generator_mem F 2)))
  · change ambientAction F (rootB a) (b27 F) ∈ sparseSpan F
    rw [rootB_b27]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 27) ((sparseSpan F).smul_mem a (generator_mem F 23))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 0)))
  · change ambientAction F (rootB a) (b28 F) ∈ sparseSpan F
    rw [rootB_b28]
    exact (generator_mem F 28)
  · change ambientAction F (rootB a) (b29 F) ∈ sparseSpan F
    rw [rootB_b29]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 29) ((sparseSpan F).smul_mem a (generator_mem F 9))) ((sparseSpan F).smul_mem a (generator_mem F 24))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 1)))
  · change ambientAction F (rootB a) (b30 F) ∈ sparseSpan F
    rw [rootB_b30]
    exact ((sparseSpan F).add_mem (generator_mem F 30) ((sparseSpan F).smul_mem a (generator_mem F 17)))
  · change ambientAction F (rootB a) (b31 F) ∈ sparseSpan F
    rw [rootB_b31]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 31) ((sparseSpan F).smul_mem a (generator_mem F 28))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 3)))
  · change ambientAction F (rootB a) (b32 F) ∈ sparseSpan F
    rw [rootB_b32]
    exact ((sparseSpan F).add_mem (generator_mem F 32) ((sparseSpan F).smul_mem (a^2) (generator_mem F 1)))
  · change ambientAction F (rootB a) (b33 F) ∈ sparseSpan F
    rw [rootB_b33]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 33) ((sparseSpan F).smul_mem a (generator_mem F 10))) ((sparseSpan F).smul_mem a (generator_mem F 25))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 5)))
  · change ambientAction F (rootB a) (b34 F) ∈ sparseSpan F
    rw [rootB_b34]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 34) ((sparseSpan F).smul_mem a (generator_mem F 20))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 13)))
  · change ambientAction F (rootB a) (b35 F) ∈ sparseSpan F
    rw [rootB_b35]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 35) ((sparseSpan F).smul_mem a (generator_mem F 32))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 24))) ((sparseSpan F).smul_mem (a^3) (generator_mem F 1)))
  · change ambientAction F (rootB a) (b36 F) ∈ sparseSpan F
    rw [rootB_b36]
    exact ((sparseSpan F).add_mem (generator_mem F 36) ((sparseSpan F).smul_mem a (generator_mem F 1)))
  · change ambientAction F (rootB a) (b37 F) ∈ sparseSpan F
    rw [rootB_b37]
    exact (generator_mem F 37)
  · change ambientAction F (rootB a) (b38 F) ∈ sparseSpan F
    rw [rootB_b38]
    exact (generator_mem F 38)
  · change ambientAction F (rootB a) (b39 F) ∈ sparseSpan F
    rw [rootB_b39]
    exact ((sparseSpan F).add_mem (generator_mem F 39) ((sparseSpan F).smul_mem a (generator_mem F 3)))
  · change ambientAction F (rootB a) (b40 F) ∈ sparseSpan F
    rw [rootB_b40]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 40) ((sparseSpan F).smul_mem a (generator_mem F 9))) ((sparseSpan F).smul_mem a (generator_mem F 36)))
  · change ambientAction F (rootB a) (b41 F) ∈ sparseSpan F
    rw [rootB_b41]
    exact (generator_mem F 41)
  · change ambientAction F (rootB a) (b42 F) ∈ sparseSpan F
    rw [rootB_b42]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 42) ((sparseSpan F).smul_mem a (generator_mem F 17))) ((sparseSpan F).smul_mem a (generator_mem F 37)))
  · change ambientAction F (rootB a) (b43 F) ∈ sparseSpan F
    rw [rootB_b43]
    exact (generator_mem F 43)
  · change ambientAction F (rootB a) (b44 F) ∈ sparseSpan F
    rw [rootB_b44]
    exact ((sparseSpan F).add_mem (generator_mem F 44) ((sparseSpan F).smul_mem a (generator_mem F 41)))
  · change ambientAction F (rootB a) (b45 F) ∈ sparseSpan F
    rw [rootB_b45]
    exact ((sparseSpan F).add_mem (generator_mem F 45) ((sparseSpan F).smul_mem a (generator_mem F 17)))
  · change ambientAction F (rootB a) (b46 F) ∈ sparseSpan F
    rw [rootB_b46]
    exact ((sparseSpan F).add_mem (generator_mem F 46) ((sparseSpan F).smul_mem a (generator_mem F 38)))
  · change ambientAction F (rootB a) (b47 F) ∈ sparseSpan F
    rw [rootB_b47]
    exact ((sparseSpan F).add_mem (generator_mem F 47) ((sparseSpan F).smul_mem a (generator_mem F 19)))
  · change ambientAction F (rootB a) (b48 F) ∈ sparseSpan F
    rw [rootB_b48]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 48) ((sparseSpan F).smul_mem a (generator_mem F 30))) ((sparseSpan F).smul_mem a (generator_mem F 45))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 37)))
  · change ambientAction F (rootB a) (b49 F) ∈ sparseSpan F
    rw [rootB_b49]
    exact ((sparseSpan F).add_mem (generator_mem F 49) ((sparseSpan F).smul_mem a (generator_mem F 43)))
  · change ambientAction F (rootB a) (b50 F) ∈ sparseSpan F
    rw [rootB_b50]
    exact ((sparseSpan F).add_mem (generator_mem F 50) ((sparseSpan F).smul_mem a (generator_mem F 12)))
  · change ambientAction F (rootB a) (b51 F) ∈ sparseSpan F
    rw [rootB_b51]
    exact ((sparseSpan F).add_mem (generator_mem F 51) ((sparseSpan F).smul_mem a (generator_mem F 13)))
  · change ambientAction F (rootB a) (b52 F) ∈ sparseSpan F
    rw [rootB_b52]
    exact ((sparseSpan F).add_mem (generator_mem F 52) ((sparseSpan F).smul_mem a (generator_mem F 14)))
  · change ambientAction F (rootB a) (b53 F) ∈ sparseSpan F
    rw [rootB_b53]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 53) ((sparseSpan F).smul_mem a (generator_mem F 15))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 1)))
  · change ambientAction F (rootB a) (b54 F) ∈ sparseSpan F
    rw [rootB_b54]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 54) ((sparseSpan F).smul_mem a (generator_mem F 10))) ((sparseSpan F).smul_mem a (generator_mem F 16))) ((sparseSpan F).smul_mem a (generator_mem F 50))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 5))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 12)))
  · change ambientAction F (rootB a) (b55 F) ∈ sparseSpan F
    rw [rootB_b55]
    exact ((sparseSpan F).add_mem (generator_mem F 55) ((sparseSpan F).smul_mem a (generator_mem F 17)))
  · change ambientAction F (rootB a) (b56 F) ∈ sparseSpan F
    rw [rootB_b56]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 56) ((sparseSpan F).smul_mem a (generator_mem F 18))) ((sparseSpan F).smul_mem a (generator_mem F 20))) ((sparseSpan F).smul_mem a (generator_mem F 51)))
  · change ambientAction F (rootB a) (b57 F) ∈ sparseSpan F
    rw [rootB_b57]
    exact (generator_mem F 57)
  · change ambientAction F (rootB a) (b58 F) ∈ sparseSpan F
    rw [rootB_b58]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 58) ((sparseSpan F).smul_mem a (generator_mem F 30))) ((sparseSpan F).smul_mem a (generator_mem F 55))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 17)))
  · change ambientAction F (rootB a) (b59 F) ∈ sparseSpan F
    rw [rootB_b59]
    exact ((sparseSpan F).add_mem (generator_mem F 59) ((sparseSpan F).smul_mem (a^2) (generator_mem F 13)))
  · change ambientAction F (rootB a) (b60 F) ∈ sparseSpan F
    rw [rootB_b60]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 60) ((sparseSpan F).smul_mem a (generator_mem F 21))) ((sparseSpan F).smul_mem a (generator_mem F 52))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 14)))
  · change ambientAction F (rootB a) (b61 F) ∈ sparseSpan F
    rw [rootB_b61]
    exact ((sparseSpan F).add_mem (generator_mem F 61) ((sparseSpan F).smul_mem a (generator_mem F 22)))
  · change ambientAction F (rootB a) (b62 F) ∈ sparseSpan F
    rw [rootB_b62]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 62) ((sparseSpan F).smul_mem a (generator_mem F 59))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 20))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 51))) ((sparseSpan F).smul_mem (a^3) (generator_mem F 13)))
  · change ambientAction F (rootB a) (b63 F) ∈ sparseSpan F
    rw [rootB_b63]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 63) ((sparseSpan F).smul_mem a (generator_mem F 57))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 19)))

end Atlas.G2.Restricted.Steinberg.OrbitClosure
