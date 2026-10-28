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

theorem rootE_b0 (a : F) : ambientAction F (rootE a) (b0 F) =
    b0 F := by
  simp only [b0, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b1 (a : F) : ambientAction F (rootE a) (b1 F) =
    b1 F + a • b0 F := by
  simp only [b0, b1, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b2 (a : F) : ambientAction F (rootE a) (b2 F) =
    b2 F := by
  simp only [b2, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b3 (a : F) : ambientAction F (rootE a) (b3 F) =
    b3 F + a • b2 F := by
  simp only [b2, b3, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b4 (a : F) : ambientAction F (rootE a) (b4 F) =
    b4 F := by
  simp only [b4, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b5 (a : F) : ambientAction F (rootE a) (b5 F) =
    b5 F + a • b4 F := by
  simp only [b4, b5, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b6 (a : F) : ambientAction F (rootE a) (b6 F) =
    b6 F := by
  simp only [b6, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b7 (a : F) : ambientAction F (rootE a) (b7 F) =
    b7 F := by
  simp only [b7, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b8 (a : F) : ambientAction F (rootE a) (b8 F) =
    b8 F := by
  simp only [b8, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b9 (a : F) : ambientAction F (rootE a) (b9 F) =
    b9 F + a • b7 F := by
  simp only [b7, b9, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b10 (a : F) : ambientAction F (rootE a) (b10 F) =
    b10 F + a • b8 F := by
  simp only [b8, b10, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b11 (a : F) : ambientAction F (rootE a) (b11 F) =
    b11 F := by
  simp only [b11, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b12 (a : F) : ambientAction F (rootE a) (b12 F) =
    b12 F + a • b4 F := by
  simp only [b4, b12, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b13 (a : F) : ambientAction F (rootE a) (b13 F) =
    b13 F + a • b5 F + a • b12 F + a^2 • b4 F := by
  simp only [b4, b5, b12, b13, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b14 (a : F) : ambientAction F (rootE a) (b14 F) =
    b14 F + a • b6 F := by
  simp only [b6, b14, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b15 (a : F) : ambientAction F (rootE a) (b15 F) =
    b15 F + a • b7 F := by
  simp only [b7, b15, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b16 (a : F) : ambientAction F (rootE a) (b16 F) =
    b16 F + a • b8 F := by
  simp only [b8, b16, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b17 (a : F) : ambientAction F (rootE a) (b17 F) =
    b17 F + a • b9 F + a • b15 F + a^2 • b7 F := by
  simp only [b7, b9, b15, b17, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b18 (a : F) : ambientAction F (rootE a) (b18 F) =
    b18 F + a^2 • b8 F := by
  simp only [b8, b18, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b19 (a : F) : ambientAction F (rootE a) (b19 F) =
    b19 F + a • b18 F + a^2 • b16 F + a^3 • b8 F := by
  simp only [b8, b16, b18, b19, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b20 (a : F) : ambientAction F (rootE a) (b20 F) =
    b20 F + a • b10 F + a • b16 F + a^2 • b8 F := by
  simp only [b8, b10, b16, b20, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b21 (a : F) : ambientAction F (rootE a) (b21 F) =
    b21 F := by
  simp only [b21, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b22 (a : F) : ambientAction F (rootE a) (b22 F) =
    b22 F + a • b21 F + a^2 • b11 F := by
  simp only [b11, b21, b22, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b23 (a : F) : ambientAction F (rootE a) (b23 F) =
    b23 F := by
  simp only [b23, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b24 (a : F) : ambientAction F (rootE a) (b24 F) =
    b24 F + a • b23 F := by
  simp only [b23, b24, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b25 (a : F) : ambientAction F (rootE a) (b25 F) =
    b25 F := by
  simp only [b25, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b26 (a : F) : ambientAction F (rootE a) (b26 F) =
    b26 F := by
  simp only [b26, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b27 (a : F) : ambientAction F (rootE a) (b27 F) =
    b27 F := by
  simp only [b27, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b28 (a : F) : ambientAction F (rootE a) (b28 F) =
    b28 F + a • b26 F := by
  simp only [b26, b28, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b29 (a : F) : ambientAction F (rootE a) (b29 F) =
    b29 F := by
  simp only [b29, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b30 (a : F) : ambientAction F (rootE a) (b30 F) =
    b30 F + a • b29 F + a^2 • b27 F := by
  simp only [b27, b29, b30, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b31 (a : F) : ambientAction F (rootE a) (b31 F) =
    b31 F := by
  simp only [b31, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b32 (a : F) : ambientAction F (rootE a) (b32 F) =
    b32 F + a • b27 F := by
  simp only [b27, b32, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b33 (a : F) : ambientAction F (rootE a) (b33 F) =
    b33 F := by
  simp only [b33, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b34 (a : F) : ambientAction F (rootE a) (b34 F) =
    b34 F + a • b33 F := by
  simp only [b33, b34, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b35 (a : F) : ambientAction F (rootE a) (b35 F) =
    b35 F := by
  simp only [b35, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b36 (a : F) : ambientAction F (rootE a) (b36 F) =
    b36 F + a • b23 F := by
  simp only [b23, b36, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b37 (a : F) : ambientAction F (rootE a) (b37 F) =
    b37 F + a • b24 F + a • b36 F + a^2 • b23 F := by
  simp only [b23, b24, b36, b37, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b38 (a : F) : ambientAction F (rootE a) (b38 F) =
    b38 F + a • b25 F + a^2 • b8 F := by
  simp only [b8, b25, b38, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b39 (a : F) : ambientAction F (rootE a) (b39 F) =
    b39 F + a • b26 F := by
  simp only [b26, b39, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b40 (a : F) : ambientAction F (rootE a) (b40 F) =
    b40 F + a • b27 F := by
  simp only [b27, b40, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b41 (a : F) : ambientAction F (rootE a) (b41 F) =
    b41 F + a • b28 F + a • b39 F + a^2 • b26 F := by
  simp only [b26, b28, b39, b41, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b42 (a : F) : ambientAction F (rootE a) (b42 F) =
    b42 F + a • b29 F := by
  simp only [b29, b42, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b43 (a : F) : ambientAction F (rootE a) (b43 F) =
    b43 F + a • b30 F + a • b42 F + a^2 • b29 F + a^2 • b40 F + a^3 • b27 F := by
  simp only [b27, b29, b30, b40, b42, b43, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b44 (a : F) : ambientAction F (rootE a) (b44 F) =
    b44 F + a • b31 F := by
  simp only [b31, b44, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b45 (a : F) : ambientAction F (rootE a) (b45 F) =
    b45 F + a • b32 F + a • b40 F + a^2 • b27 F := by
  simp only [b27, b32, b40, b45, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b46 (a : F) : ambientAction F (rootE a) (b46 F) =
    b46 F + a • b33 F := by
  simp only [b33, b46, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b47 (a : F) : ambientAction F (rootE a) (b47 F) =
    b47 F + a • b34 F + a • b46 F + a^2 • b33 F := by
  simp only [b33, b34, b46, b47, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b48 (a : F) : ambientAction F (rootE a) (b48 F) =
    b48 F := by
  simp only [b48, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b49 (a : F) : ambientAction F (rootE a) (b49 F) =
    b49 F + a • b48 F + a^2 • b35 F := by
  simp only [b35, b48, b49, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b50 (a : F) : ambientAction F (rootE a) (b50 F) =
    b50 F := by
  simp only [b50, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b51 (a : F) : ambientAction F (rootE a) (b51 F) =
    b51 F + a • b50 F := by
  simp only [b50, b51, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b52 (a : F) : ambientAction F (rootE a) (b52 F) =
    b52 F + a • b11 F := by
  simp only [b11, b52, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b53 (a : F) : ambientAction F (rootE a) (b53 F) =
    b53 F := by
  simp only [b53, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b54 (a : F) : ambientAction F (rootE a) (b54 F) =
    b54 F := by
  simp only [b54, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b55 (a : F) : ambientAction F (rootE a) (b55 F) =
    b55 F + a • b53 F := by
  simp only [b53, b55, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b56 (a : F) : ambientAction F (rootE a) (b56 F) =
    b56 F := by
  simp only [b56, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b57 (a : F) : ambientAction F (rootE a) (b57 F) =
    b57 F + a • b56 F + a^2 • b54 F := by
  simp only [b54, b56, b57, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b58 (a : F) : ambientAction F (rootE a) (b58 F) =
    b58 F + a • b35 F := by
  simp only [b35, b58, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b59 (a : F) : ambientAction F (rootE a) (b59 F) =
    b59 F + a • b54 F := by
  simp only [b54, b59, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b60 (a : F) : ambientAction F (rootE a) (b60 F) =
    b60 F := by
  simp only [b60, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b61 (a : F) : ambientAction F (rootE a) (b61 F) =
    b61 F + a • b60 F := by
  simp only [b60, b61, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b62 (a : F) : ambientAction F (rootE a) (b62 F) =
    b62 F := by
  simp only [b62, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem rootE_b63 (a : F) : ambientAction F (rootE a) (b63 F) =
    b63 F + a • b62 F := by
  simp only [b62, b63, map_add, ambientAction_pure, rootE_e0, rootE_e1, rootE_e2, rootE_e3, rootE_e4, rootE_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

/-- Preservation by the actual rootE elements, at every parameter. -/
theorem rootE_preserves (a : F) :
    ∀ v ∈ sparseSpan F, ambientAction F (rootE a) v ∈ sparseSpan F := by
  apply preserves_of_generators
  intro i
  fin_cases i
  · change ambientAction F (rootE a) (b0 F) ∈ sparseSpan F
    rw [rootE_b0]
    exact (generator_mem F 0)
  · change ambientAction F (rootE a) (b1 F) ∈ sparseSpan F
    rw [rootE_b1]
    exact ((sparseSpan F).add_mem (generator_mem F 1) ((sparseSpan F).smul_mem a (generator_mem F 0)))
  · change ambientAction F (rootE a) (b2 F) ∈ sparseSpan F
    rw [rootE_b2]
    exact (generator_mem F 2)
  · change ambientAction F (rootE a) (b3 F) ∈ sparseSpan F
    rw [rootE_b3]
    exact ((sparseSpan F).add_mem (generator_mem F 3) ((sparseSpan F).smul_mem a (generator_mem F 2)))
  · change ambientAction F (rootE a) (b4 F) ∈ sparseSpan F
    rw [rootE_b4]
    exact (generator_mem F 4)
  · change ambientAction F (rootE a) (b5 F) ∈ sparseSpan F
    rw [rootE_b5]
    exact ((sparseSpan F).add_mem (generator_mem F 5) ((sparseSpan F).smul_mem a (generator_mem F 4)))
  · change ambientAction F (rootE a) (b6 F) ∈ sparseSpan F
    rw [rootE_b6]
    exact (generator_mem F 6)
  · change ambientAction F (rootE a) (b7 F) ∈ sparseSpan F
    rw [rootE_b7]
    exact (generator_mem F 7)
  · change ambientAction F (rootE a) (b8 F) ∈ sparseSpan F
    rw [rootE_b8]
    exact (generator_mem F 8)
  · change ambientAction F (rootE a) (b9 F) ∈ sparseSpan F
    rw [rootE_b9]
    exact ((sparseSpan F).add_mem (generator_mem F 9) ((sparseSpan F).smul_mem a (generator_mem F 7)))
  · change ambientAction F (rootE a) (b10 F) ∈ sparseSpan F
    rw [rootE_b10]
    exact ((sparseSpan F).add_mem (generator_mem F 10) ((sparseSpan F).smul_mem a (generator_mem F 8)))
  · change ambientAction F (rootE a) (b11 F) ∈ sparseSpan F
    rw [rootE_b11]
    exact (generator_mem F 11)
  · change ambientAction F (rootE a) (b12 F) ∈ sparseSpan F
    rw [rootE_b12]
    exact ((sparseSpan F).add_mem (generator_mem F 12) ((sparseSpan F).smul_mem a (generator_mem F 4)))
  · change ambientAction F (rootE a) (b13 F) ∈ sparseSpan F
    rw [rootE_b13]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 13) ((sparseSpan F).smul_mem a (generator_mem F 5))) ((sparseSpan F).smul_mem a (generator_mem F 12))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 4)))
  · change ambientAction F (rootE a) (b14 F) ∈ sparseSpan F
    rw [rootE_b14]
    exact ((sparseSpan F).add_mem (generator_mem F 14) ((sparseSpan F).smul_mem a (generator_mem F 6)))
  · change ambientAction F (rootE a) (b15 F) ∈ sparseSpan F
    rw [rootE_b15]
    exact ((sparseSpan F).add_mem (generator_mem F 15) ((sparseSpan F).smul_mem a (generator_mem F 7)))
  · change ambientAction F (rootE a) (b16 F) ∈ sparseSpan F
    rw [rootE_b16]
    exact ((sparseSpan F).add_mem (generator_mem F 16) ((sparseSpan F).smul_mem a (generator_mem F 8)))
  · change ambientAction F (rootE a) (b17 F) ∈ sparseSpan F
    rw [rootE_b17]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 17) ((sparseSpan F).smul_mem a (generator_mem F 9))) ((sparseSpan F).smul_mem a (generator_mem F 15))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 7)))
  · change ambientAction F (rootE a) (b18 F) ∈ sparseSpan F
    rw [rootE_b18]
    exact ((sparseSpan F).add_mem (generator_mem F 18) ((sparseSpan F).smul_mem (a^2) (generator_mem F 8)))
  · change ambientAction F (rootE a) (b19 F) ∈ sparseSpan F
    rw [rootE_b19]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 19) ((sparseSpan F).smul_mem a (generator_mem F 18))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 16))) ((sparseSpan F).smul_mem (a^3) (generator_mem F 8)))
  · change ambientAction F (rootE a) (b20 F) ∈ sparseSpan F
    rw [rootE_b20]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 20) ((sparseSpan F).smul_mem a (generator_mem F 10))) ((sparseSpan F).smul_mem a (generator_mem F 16))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 8)))
  · change ambientAction F (rootE a) (b21 F) ∈ sparseSpan F
    rw [rootE_b21]
    exact (generator_mem F 21)
  · change ambientAction F (rootE a) (b22 F) ∈ sparseSpan F
    rw [rootE_b22]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 22) ((sparseSpan F).smul_mem a (generator_mem F 21))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 11)))
  · change ambientAction F (rootE a) (b23 F) ∈ sparseSpan F
    rw [rootE_b23]
    exact (generator_mem F 23)
  · change ambientAction F (rootE a) (b24 F) ∈ sparseSpan F
    rw [rootE_b24]
    exact ((sparseSpan F).add_mem (generator_mem F 24) ((sparseSpan F).smul_mem a (generator_mem F 23)))
  · change ambientAction F (rootE a) (b25 F) ∈ sparseSpan F
    rw [rootE_b25]
    exact (generator_mem F 25)
  · change ambientAction F (rootE a) (b26 F) ∈ sparseSpan F
    rw [rootE_b26]
    exact (generator_mem F 26)
  · change ambientAction F (rootE a) (b27 F) ∈ sparseSpan F
    rw [rootE_b27]
    exact (generator_mem F 27)
  · change ambientAction F (rootE a) (b28 F) ∈ sparseSpan F
    rw [rootE_b28]
    exact ((sparseSpan F).add_mem (generator_mem F 28) ((sparseSpan F).smul_mem a (generator_mem F 26)))
  · change ambientAction F (rootE a) (b29 F) ∈ sparseSpan F
    rw [rootE_b29]
    exact (generator_mem F 29)
  · change ambientAction F (rootE a) (b30 F) ∈ sparseSpan F
    rw [rootE_b30]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 30) ((sparseSpan F).smul_mem a (generator_mem F 29))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 27)))
  · change ambientAction F (rootE a) (b31 F) ∈ sparseSpan F
    rw [rootE_b31]
    exact (generator_mem F 31)
  · change ambientAction F (rootE a) (b32 F) ∈ sparseSpan F
    rw [rootE_b32]
    exact ((sparseSpan F).add_mem (generator_mem F 32) ((sparseSpan F).smul_mem a (generator_mem F 27)))
  · change ambientAction F (rootE a) (b33 F) ∈ sparseSpan F
    rw [rootE_b33]
    exact (generator_mem F 33)
  · change ambientAction F (rootE a) (b34 F) ∈ sparseSpan F
    rw [rootE_b34]
    exact ((sparseSpan F).add_mem (generator_mem F 34) ((sparseSpan F).smul_mem a (generator_mem F 33)))
  · change ambientAction F (rootE a) (b35 F) ∈ sparseSpan F
    rw [rootE_b35]
    exact (generator_mem F 35)
  · change ambientAction F (rootE a) (b36 F) ∈ sparseSpan F
    rw [rootE_b36]
    exact ((sparseSpan F).add_mem (generator_mem F 36) ((sparseSpan F).smul_mem a (generator_mem F 23)))
  · change ambientAction F (rootE a) (b37 F) ∈ sparseSpan F
    rw [rootE_b37]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 37) ((sparseSpan F).smul_mem a (generator_mem F 24))) ((sparseSpan F).smul_mem a (generator_mem F 36))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 23)))
  · change ambientAction F (rootE a) (b38 F) ∈ sparseSpan F
    rw [rootE_b38]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 38) ((sparseSpan F).smul_mem a (generator_mem F 25))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 8)))
  · change ambientAction F (rootE a) (b39 F) ∈ sparseSpan F
    rw [rootE_b39]
    exact ((sparseSpan F).add_mem (generator_mem F 39) ((sparseSpan F).smul_mem a (generator_mem F 26)))
  · change ambientAction F (rootE a) (b40 F) ∈ sparseSpan F
    rw [rootE_b40]
    exact ((sparseSpan F).add_mem (generator_mem F 40) ((sparseSpan F).smul_mem a (generator_mem F 27)))
  · change ambientAction F (rootE a) (b41 F) ∈ sparseSpan F
    rw [rootE_b41]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 41) ((sparseSpan F).smul_mem a (generator_mem F 28))) ((sparseSpan F).smul_mem a (generator_mem F 39))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 26)))
  · change ambientAction F (rootE a) (b42 F) ∈ sparseSpan F
    rw [rootE_b42]
    exact ((sparseSpan F).add_mem (generator_mem F 42) ((sparseSpan F).smul_mem a (generator_mem F 29)))
  · change ambientAction F (rootE a) (b43 F) ∈ sparseSpan F
    rw [rootE_b43]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 43) ((sparseSpan F).smul_mem a (generator_mem F 30))) ((sparseSpan F).smul_mem a (generator_mem F 42))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 29))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 40))) ((sparseSpan F).smul_mem (a^3) (generator_mem F 27)))
  · change ambientAction F (rootE a) (b44 F) ∈ sparseSpan F
    rw [rootE_b44]
    exact ((sparseSpan F).add_mem (generator_mem F 44) ((sparseSpan F).smul_mem a (generator_mem F 31)))
  · change ambientAction F (rootE a) (b45 F) ∈ sparseSpan F
    rw [rootE_b45]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 45) ((sparseSpan F).smul_mem a (generator_mem F 32))) ((sparseSpan F).smul_mem a (generator_mem F 40))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 27)))
  · change ambientAction F (rootE a) (b46 F) ∈ sparseSpan F
    rw [rootE_b46]
    exact ((sparseSpan F).add_mem (generator_mem F 46) ((sparseSpan F).smul_mem a (generator_mem F 33)))
  · change ambientAction F (rootE a) (b47 F) ∈ sparseSpan F
    rw [rootE_b47]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 47) ((sparseSpan F).smul_mem a (generator_mem F 34))) ((sparseSpan F).smul_mem a (generator_mem F 46))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 33)))
  · change ambientAction F (rootE a) (b48 F) ∈ sparseSpan F
    rw [rootE_b48]
    exact (generator_mem F 48)
  · change ambientAction F (rootE a) (b49 F) ∈ sparseSpan F
    rw [rootE_b49]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 49) ((sparseSpan F).smul_mem a (generator_mem F 48))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 35)))
  · change ambientAction F (rootE a) (b50 F) ∈ sparseSpan F
    rw [rootE_b50]
    exact (generator_mem F 50)
  · change ambientAction F (rootE a) (b51 F) ∈ sparseSpan F
    rw [rootE_b51]
    exact ((sparseSpan F).add_mem (generator_mem F 51) ((sparseSpan F).smul_mem a (generator_mem F 50)))
  · change ambientAction F (rootE a) (b52 F) ∈ sparseSpan F
    rw [rootE_b52]
    exact ((sparseSpan F).add_mem (generator_mem F 52) ((sparseSpan F).smul_mem a (generator_mem F 11)))
  · change ambientAction F (rootE a) (b53 F) ∈ sparseSpan F
    rw [rootE_b53]
    exact (generator_mem F 53)
  · change ambientAction F (rootE a) (b54 F) ∈ sparseSpan F
    rw [rootE_b54]
    exact (generator_mem F 54)
  · change ambientAction F (rootE a) (b55 F) ∈ sparseSpan F
    rw [rootE_b55]
    exact ((sparseSpan F).add_mem (generator_mem F 55) ((sparseSpan F).smul_mem a (generator_mem F 53)))
  · change ambientAction F (rootE a) (b56 F) ∈ sparseSpan F
    rw [rootE_b56]
    exact (generator_mem F 56)
  · change ambientAction F (rootE a) (b57 F) ∈ sparseSpan F
    rw [rootE_b57]
    exact ((sparseSpan F).add_mem ((sparseSpan F).add_mem (generator_mem F 57) ((sparseSpan F).smul_mem a (generator_mem F 56))) ((sparseSpan F).smul_mem (a^2) (generator_mem F 54)))
  · change ambientAction F (rootE a) (b58 F) ∈ sparseSpan F
    rw [rootE_b58]
    exact ((sparseSpan F).add_mem (generator_mem F 58) ((sparseSpan F).smul_mem a (generator_mem F 35)))
  · change ambientAction F (rootE a) (b59 F) ∈ sparseSpan F
    rw [rootE_b59]
    exact ((sparseSpan F).add_mem (generator_mem F 59) ((sparseSpan F).smul_mem a (generator_mem F 54)))
  · change ambientAction F (rootE a) (b60 F) ∈ sparseSpan F
    rw [rootE_b60]
    exact (generator_mem F 60)
  · change ambientAction F (rootE a) (b61 F) ∈ sparseSpan F
    rw [rootE_b61]
    exact ((sparseSpan F).add_mem (generator_mem F 61) ((sparseSpan F).smul_mem a (generator_mem F 60)))
  · change ambientAction F (rootE a) (b62 F) ∈ sparseSpan F
    rw [rootE_b62]
    exact (generator_mem F 62)
  · change ambientAction F (rootE a) (b63 F) ∈ sparseSpan F
    rw [rootE_b63]
    exact ((sparseSpan F).add_mem (generator_mem F 63) ((sparseSpan F).smul_mem a (generator_mem F 62)))

end Atlas.G2.Restricted.Steinberg.OrbitClosure
