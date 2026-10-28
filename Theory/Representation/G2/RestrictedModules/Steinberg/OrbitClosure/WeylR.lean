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

theorem weylR_b0 : ambientAction F weylR (b0 F) =
    b1 F := by
  simp only [b0, b1, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b1 : ambientAction F weylR (b1 F) =
    b0 F := by
  simp only [b0, b1, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b2 : ambientAction F weylR (b2 F) =
    b3 F := by
  simp only [b2, b3, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b3 : ambientAction F weylR (b3 F) =
    b2 F := by
  simp only [b2, b3, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b4 : ambientAction F weylR (b4 F) =
    b13 F := by
  simp only [b4, b13, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b5 : ambientAction F weylR (b5 F) =
    b12 F := by
  simp only [b5, b12, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b6 : ambientAction F weylR (b6 F) =
    b14 F := by
  simp only [b6, b14, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b7 : ambientAction F weylR (b7 F) =
    b17 F := by
  simp only [b7, b17, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b8 : ambientAction F weylR (b8 F) =
    b19 F := by
  simp only [b8, b19, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b9 : ambientAction F weylR (b9 F) =
    b15 F := by
  simp only [b9, b15, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b10 : ambientAction F weylR (b10 F) =
    b20 F := by
  simp only [b10, b20, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b11 : ambientAction F weylR (b11 F) =
    b22 F := by
  simp only [b11, b22, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b12 : ambientAction F weylR (b12 F) =
    b5 F := by
  simp only [b5, b12, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b13 : ambientAction F weylR (b13 F) =
    b4 F := by
  simp only [b4, b13, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b14 : ambientAction F weylR (b14 F) =
    b6 F := by
  simp only [b6, b14, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b15 : ambientAction F weylR (b15 F) =
    b9 F := by
  simp only [b9, b15, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b16 : ambientAction F weylR (b16 F) =
    b18 F := by
  simp only [b16, b18, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b17 : ambientAction F weylR (b17 F) =
    b7 F := by
  simp only [b7, b17, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b18 : ambientAction F weylR (b18 F) =
    b16 F := by
  simp only [b16, b18, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b19 : ambientAction F weylR (b19 F) =
    b8 F := by
  simp only [b8, b19, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b20 : ambientAction F weylR (b20 F) =
    b10 F := by
  simp only [b10, b20, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b21 : ambientAction F weylR (b21 F) =
    b21 F := by
  simp only [b21, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b22 : ambientAction F weylR (b22 F) =
    b11 F := by
  simp only [b11, b22, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b23 : ambientAction F weylR (b23 F) =
    b37 F := by
  simp only [b23, b37, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b24 : ambientAction F weylR (b24 F) =
    b36 F := by
  simp only [b24, b36, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b25 : ambientAction F weylR (b25 F) =
    b18 F + b38 F := by
  simp only [b18, b25, b38, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b26 : ambientAction F weylR (b26 F) =
    b41 F := by
  simp only [b26, b41, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b27 : ambientAction F weylR (b27 F) =
    b43 F := by
  simp only [b27, b43, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b28 : ambientAction F weylR (b28 F) =
    b39 F := by
  simp only [b28, b39, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b29 : ambientAction F weylR (b29 F) =
    b42 F := by
  simp only [b29, b42, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b30 : ambientAction F weylR (b30 F) =
    b40 F := by
  simp only [b30, b40, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b31 : ambientAction F weylR (b31 F) =
    b44 F := by
  simp only [b31, b44, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b32 : ambientAction F weylR (b32 F) =
    b42 F + b45 F := by
  simp only [b32, b42, b45, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b33 : ambientAction F weylR (b33 F) =
    b47 F := by
  simp only [b33, b47, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b34 : ambientAction F weylR (b34 F) =
    b46 F := by
  simp only [b34, b46, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b35 : ambientAction F weylR (b35 F) =
    b49 F := by
  simp only [b35, b49, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b36 : ambientAction F weylR (b36 F) =
    b24 F := by
  simp only [b24, b36, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b37 : ambientAction F weylR (b37 F) =
    b23 F := by
  simp only [b23, b37, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b38 : ambientAction F weylR (b38 F) =
    b16 F + b25 F := by
  simp only [b16, b25, b38, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b39 : ambientAction F weylR (b39 F) =
    b28 F := by
  simp only [b28, b39, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b40 : ambientAction F weylR (b40 F) =
    b30 F := by
  simp only [b30, b40, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b41 : ambientAction F weylR (b41 F) =
    b26 F := by
  simp only [b26, b41, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b42 : ambientAction F weylR (b42 F) =
    b29 F := by
  simp only [b29, b42, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b43 : ambientAction F weylR (b43 F) =
    b27 F := by
  simp only [b27, b43, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b44 : ambientAction F weylR (b44 F) =
    b31 F := by
  simp only [b31, b44, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b45 : ambientAction F weylR (b45 F) =
    b29 F + b32 F := by
  simp only [b29, b32, b45, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b46 : ambientAction F weylR (b46 F) =
    b34 F := by
  simp only [b34, b46, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b47 : ambientAction F weylR (b47 F) =
    b33 F := by
  simp only [b33, b47, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b48 : ambientAction F weylR (b48 F) =
    b48 F := by
  simp only [b48, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b49 : ambientAction F weylR (b49 F) =
    b35 F := by
  simp only [b35, b49, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b50 : ambientAction F weylR (b50 F) =
    b51 F := by
  simp only [b50, b51, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b51 : ambientAction F weylR (b51 F) =
    b50 F := by
  simp only [b50, b51, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b52 : ambientAction F weylR (b52 F) =
    b21 F + b52 F := by
  simp only [b21, b52, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b53 : ambientAction F weylR (b53 F) =
    b55 F := by
  simp only [b53, b55, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b54 : ambientAction F weylR (b54 F) =
    b57 F := by
  simp only [b54, b57, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b55 : ambientAction F weylR (b55 F) =
    b53 F := by
  simp only [b53, b55, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b56 : ambientAction F weylR (b56 F) =
    b56 F := by
  simp only [b56, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b57 : ambientAction F weylR (b57 F) =
    b54 F := by
  simp only [b54, b57, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b58 : ambientAction F weylR (b58 F) =
    b48 F + b58 F := by
  simp only [b48, b58, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b59 : ambientAction F weylR (b59 F) =
    b56 F + b59 F := by
  simp only [b56, b59, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b60 : ambientAction F weylR (b60 F) =
    b61 F := by
  simp only [b60, b61, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b61 : ambientAction F weylR (b61 F) =
    b60 F := by
  simp only [b60, b61, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b62 : ambientAction F weylR (b62 F) =
    b63 F := by
  simp only [b62, b63, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylR_b63 : ambientAction F weylR (b63 F) =
    b62 F := by
  simp only [b62, b63, map_add, ambientAction_pure, weylR_e0, weylR_e1, weylR_e2, weylR_e3, weylR_e4, weylR_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

/-- Preservation by the actual weylR elements, at every parameter. -/
theorem weylR_preserves :
    ∀ v ∈ sparseSpan F, ambientAction F weylR v ∈ sparseSpan F := by
  apply preserves_of_generators
  intro i
  fin_cases i
  · change ambientAction F weylR (b0 F) ∈ sparseSpan F
    rw [weylR_b0]
    exact (generator_mem F 1)
  · change ambientAction F weylR (b1 F) ∈ sparseSpan F
    rw [weylR_b1]
    exact (generator_mem F 0)
  · change ambientAction F weylR (b2 F) ∈ sparseSpan F
    rw [weylR_b2]
    exact (generator_mem F 3)
  · change ambientAction F weylR (b3 F) ∈ sparseSpan F
    rw [weylR_b3]
    exact (generator_mem F 2)
  · change ambientAction F weylR (b4 F) ∈ sparseSpan F
    rw [weylR_b4]
    exact (generator_mem F 13)
  · change ambientAction F weylR (b5 F) ∈ sparseSpan F
    rw [weylR_b5]
    exact (generator_mem F 12)
  · change ambientAction F weylR (b6 F) ∈ sparseSpan F
    rw [weylR_b6]
    exact (generator_mem F 14)
  · change ambientAction F weylR (b7 F) ∈ sparseSpan F
    rw [weylR_b7]
    exact (generator_mem F 17)
  · change ambientAction F weylR (b8 F) ∈ sparseSpan F
    rw [weylR_b8]
    exact (generator_mem F 19)
  · change ambientAction F weylR (b9 F) ∈ sparseSpan F
    rw [weylR_b9]
    exact (generator_mem F 15)
  · change ambientAction F weylR (b10 F) ∈ sparseSpan F
    rw [weylR_b10]
    exact (generator_mem F 20)
  · change ambientAction F weylR (b11 F) ∈ sparseSpan F
    rw [weylR_b11]
    exact (generator_mem F 22)
  · change ambientAction F weylR (b12 F) ∈ sparseSpan F
    rw [weylR_b12]
    exact (generator_mem F 5)
  · change ambientAction F weylR (b13 F) ∈ sparseSpan F
    rw [weylR_b13]
    exact (generator_mem F 4)
  · change ambientAction F weylR (b14 F) ∈ sparseSpan F
    rw [weylR_b14]
    exact (generator_mem F 6)
  · change ambientAction F weylR (b15 F) ∈ sparseSpan F
    rw [weylR_b15]
    exact (generator_mem F 9)
  · change ambientAction F weylR (b16 F) ∈ sparseSpan F
    rw [weylR_b16]
    exact (generator_mem F 18)
  · change ambientAction F weylR (b17 F) ∈ sparseSpan F
    rw [weylR_b17]
    exact (generator_mem F 7)
  · change ambientAction F weylR (b18 F) ∈ sparseSpan F
    rw [weylR_b18]
    exact (generator_mem F 16)
  · change ambientAction F weylR (b19 F) ∈ sparseSpan F
    rw [weylR_b19]
    exact (generator_mem F 8)
  · change ambientAction F weylR (b20 F) ∈ sparseSpan F
    rw [weylR_b20]
    exact (generator_mem F 10)
  · change ambientAction F weylR (b21 F) ∈ sparseSpan F
    rw [weylR_b21]
    exact (generator_mem F 21)
  · change ambientAction F weylR (b22 F) ∈ sparseSpan F
    rw [weylR_b22]
    exact (generator_mem F 11)
  · change ambientAction F weylR (b23 F) ∈ sparseSpan F
    rw [weylR_b23]
    exact (generator_mem F 37)
  · change ambientAction F weylR (b24 F) ∈ sparseSpan F
    rw [weylR_b24]
    exact (generator_mem F 36)
  · change ambientAction F weylR (b25 F) ∈ sparseSpan F
    rw [weylR_b25]
    exact ((sparseSpan F).add_mem (generator_mem F 18) (generator_mem F 38))
  · change ambientAction F weylR (b26 F) ∈ sparseSpan F
    rw [weylR_b26]
    exact (generator_mem F 41)
  · change ambientAction F weylR (b27 F) ∈ sparseSpan F
    rw [weylR_b27]
    exact (generator_mem F 43)
  · change ambientAction F weylR (b28 F) ∈ sparseSpan F
    rw [weylR_b28]
    exact (generator_mem F 39)
  · change ambientAction F weylR (b29 F) ∈ sparseSpan F
    rw [weylR_b29]
    exact (generator_mem F 42)
  · change ambientAction F weylR (b30 F) ∈ sparseSpan F
    rw [weylR_b30]
    exact (generator_mem F 40)
  · change ambientAction F weylR (b31 F) ∈ sparseSpan F
    rw [weylR_b31]
    exact (generator_mem F 44)
  · change ambientAction F weylR (b32 F) ∈ sparseSpan F
    rw [weylR_b32]
    exact ((sparseSpan F).add_mem (generator_mem F 42) (generator_mem F 45))
  · change ambientAction F weylR (b33 F) ∈ sparseSpan F
    rw [weylR_b33]
    exact (generator_mem F 47)
  · change ambientAction F weylR (b34 F) ∈ sparseSpan F
    rw [weylR_b34]
    exact (generator_mem F 46)
  · change ambientAction F weylR (b35 F) ∈ sparseSpan F
    rw [weylR_b35]
    exact (generator_mem F 49)
  · change ambientAction F weylR (b36 F) ∈ sparseSpan F
    rw [weylR_b36]
    exact (generator_mem F 24)
  · change ambientAction F weylR (b37 F) ∈ sparseSpan F
    rw [weylR_b37]
    exact (generator_mem F 23)
  · change ambientAction F weylR (b38 F) ∈ sparseSpan F
    rw [weylR_b38]
    exact ((sparseSpan F).add_mem (generator_mem F 16) (generator_mem F 25))
  · change ambientAction F weylR (b39 F) ∈ sparseSpan F
    rw [weylR_b39]
    exact (generator_mem F 28)
  · change ambientAction F weylR (b40 F) ∈ sparseSpan F
    rw [weylR_b40]
    exact (generator_mem F 30)
  · change ambientAction F weylR (b41 F) ∈ sparseSpan F
    rw [weylR_b41]
    exact (generator_mem F 26)
  · change ambientAction F weylR (b42 F) ∈ sparseSpan F
    rw [weylR_b42]
    exact (generator_mem F 29)
  · change ambientAction F weylR (b43 F) ∈ sparseSpan F
    rw [weylR_b43]
    exact (generator_mem F 27)
  · change ambientAction F weylR (b44 F) ∈ sparseSpan F
    rw [weylR_b44]
    exact (generator_mem F 31)
  · change ambientAction F weylR (b45 F) ∈ sparseSpan F
    rw [weylR_b45]
    exact ((sparseSpan F).add_mem (generator_mem F 29) (generator_mem F 32))
  · change ambientAction F weylR (b46 F) ∈ sparseSpan F
    rw [weylR_b46]
    exact (generator_mem F 34)
  · change ambientAction F weylR (b47 F) ∈ sparseSpan F
    rw [weylR_b47]
    exact (generator_mem F 33)
  · change ambientAction F weylR (b48 F) ∈ sparseSpan F
    rw [weylR_b48]
    exact (generator_mem F 48)
  · change ambientAction F weylR (b49 F) ∈ sparseSpan F
    rw [weylR_b49]
    exact (generator_mem F 35)
  · change ambientAction F weylR (b50 F) ∈ sparseSpan F
    rw [weylR_b50]
    exact (generator_mem F 51)
  · change ambientAction F weylR (b51 F) ∈ sparseSpan F
    rw [weylR_b51]
    exact (generator_mem F 50)
  · change ambientAction F weylR (b52 F) ∈ sparseSpan F
    rw [weylR_b52]
    exact ((sparseSpan F).add_mem (generator_mem F 21) (generator_mem F 52))
  · change ambientAction F weylR (b53 F) ∈ sparseSpan F
    rw [weylR_b53]
    exact (generator_mem F 55)
  · change ambientAction F weylR (b54 F) ∈ sparseSpan F
    rw [weylR_b54]
    exact (generator_mem F 57)
  · change ambientAction F weylR (b55 F) ∈ sparseSpan F
    rw [weylR_b55]
    exact (generator_mem F 53)
  · change ambientAction F weylR (b56 F) ∈ sparseSpan F
    rw [weylR_b56]
    exact (generator_mem F 56)
  · change ambientAction F weylR (b57 F) ∈ sparseSpan F
    rw [weylR_b57]
    exact (generator_mem F 54)
  · change ambientAction F weylR (b58 F) ∈ sparseSpan F
    rw [weylR_b58]
    exact ((sparseSpan F).add_mem (generator_mem F 48) (generator_mem F 58))
  · change ambientAction F weylR (b59 F) ∈ sparseSpan F
    rw [weylR_b59]
    exact ((sparseSpan F).add_mem (generator_mem F 56) (generator_mem F 59))
  · change ambientAction F weylR (b60 F) ∈ sparseSpan F
    rw [weylR_b60]
    exact (generator_mem F 61)
  · change ambientAction F weylR (b61 F) ∈ sparseSpan F
    rw [weylR_b61]
    exact (generator_mem F 60)
  · change ambientAction F weylR (b62 F) ∈ sparseSpan F
    rw [weylR_b62]
    exact (generator_mem F 63)
  · change ambientAction F weylR (b63 F) ∈ sparseSpan F
    rw [weylR_b63]
    exact (generator_mem F 62)

end Atlas.G2.Restricted.Steinberg.OrbitClosure
