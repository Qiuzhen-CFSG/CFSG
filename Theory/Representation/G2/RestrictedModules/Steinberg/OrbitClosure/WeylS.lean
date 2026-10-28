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

theorem weylS_b0 : ambientAction F weylS (b0 F) =
    b4 F := by
  simp only [b0, b4, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b1 : ambientAction F weylS (b1 F) =
    b8 F := by
  simp only [b1, b8, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b2 : ambientAction F weylS (b2 F) =
    b6 F := by
  simp only [b2, b6, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b3 : ambientAction F weylS (b3 F) =
    b11 F := by
  simp only [b3, b11, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b4 : ambientAction F weylS (b4 F) =
    b0 F := by
  simp only [b0, b4, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b5 : ambientAction F weylS (b5 F) =
    b7 F := by
  simp only [b5, b7, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b6 : ambientAction F weylS (b6 F) =
    b2 F := by
  simp only [b2, b6, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b7 : ambientAction F weylS (b7 F) =
    b5 F := by
  simp only [b5, b7, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b8 : ambientAction F weylS (b8 F) =
    b1 F := by
  simp only [b1, b8, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b9 : ambientAction F weylS (b9 F) =
    b10 F := by
  simp only [b9, b10, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b10 : ambientAction F weylS (b10 F) =
    b9 F := by
  simp only [b9, b10, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b11 : ambientAction F weylS (b11 F) =
    b3 F := by
  simp only [b3, b11, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b12 : ambientAction F weylS (b12 F) =
    b7 F + b23 F := by
  simp only [b7, b12, b23, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b13 : ambientAction F weylS (b13 F) =
    b27 F := by
  simp only [b13, b27, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b14 : ambientAction F weylS (b14 F) =
    b26 F := by
  simp only [b14, b26, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b15 : ambientAction F weylS (b15 F) =
    b25 F := by
  simp only [b15, b25, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b16 : ambientAction F weylS (b16 F) =
    b24 F := by
  simp only [b16, b24, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b17 : ambientAction F weylS (b17 F) =
    b33 F := by
  simp only [b17, b33, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b18 : ambientAction F weylS (b18 F) =
    b32 F := by
  simp only [b18, b32, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b19 : ambientAction F weylS (b19 F) =
    b35 F := by
  simp only [b19, b35, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b20 : ambientAction F weylS (b20 F) =
    b29 F := by
  simp only [b20, b29, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b21 : ambientAction F weylS (b21 F) =
    b28 F := by
  simp only [b21, b28, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b22 : ambientAction F weylS (b22 F) =
    b31 F := by
  simp only [b22, b31, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b23 : ambientAction F weylS (b23 F) =
    b5 F + b12 F := by
  simp only [b5, b12, b23, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b24 : ambientAction F weylS (b24 F) =
    b16 F := by
  simp only [b16, b24, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b25 : ambientAction F weylS (b25 F) =
    b15 F := by
  simp only [b15, b25, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b26 : ambientAction F weylS (b26 F) =
    b14 F := by
  simp only [b14, b26, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b27 : ambientAction F weylS (b27 F) =
    b13 F := by
  simp only [b13, b27, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b28 : ambientAction F weylS (b28 F) =
    b21 F := by
  simp only [b21, b28, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b29 : ambientAction F weylS (b29 F) =
    b20 F := by
  simp only [b20, b29, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b30 : ambientAction F weylS (b30 F) =
    b34 F := by
  simp only [b30, b34, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b31 : ambientAction F weylS (b31 F) =
    b22 F := by
  simp only [b22, b31, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b32 : ambientAction F weylS (b32 F) =
    b18 F := by
  simp only [b18, b32, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b33 : ambientAction F weylS (b33 F) =
    b17 F := by
  simp only [b17, b33, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b34 : ambientAction F weylS (b34 F) =
    b30 F := by
  simp only [b30, b34, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b35 : ambientAction F weylS (b35 F) =
    b19 F := by
  simp only [b19, b35, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b36 : ambientAction F weylS (b36 F) =
    b10 F + b50 F := by
  simp only [b10, b36, b50, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b37 : ambientAction F weylS (b37 F) =
    b54 F := by
  simp only [b37, b54, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b38 : ambientAction F weylS (b38 F) =
    b53 F := by
  simp only [b38, b53, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b39 : ambientAction F weylS (b39 F) =
    b52 F := by
  simp only [b39, b52, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b40 : ambientAction F weylS (b40 F) =
    b51 F := by
  simp only [b40, b51, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b41 : ambientAction F weylS (b41 F) =
    b60 F := by
  simp only [b41, b60, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b42 : ambientAction F weylS (b42 F) =
    b34 F + b59 F := by
  simp only [b34, b42, b59, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b43 : ambientAction F weylS (b43 F) =
    b62 F := by
  simp only [b43, b62, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b44 : ambientAction F weylS (b44 F) =
    b61 F := by
  simp only [b44, b61, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b45 : ambientAction F weylS (b45 F) =
    b34 F + b56 F := by
  simp only [b34, b45, b56, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b46 : ambientAction F weylS (b46 F) =
    b55 F := by
  simp only [b46, b55, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b47 : ambientAction F weylS (b47 F) =
    b58 F := by
  simp only [b47, b58, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b48 : ambientAction F weylS (b48 F) =
    b57 F := by
  simp only [b48, b57, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b49 : ambientAction F weylS (b49 F) =
    b63 F := by
  simp only [b49, b63, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b50 : ambientAction F weylS (b50 F) =
    b9 F + b36 F := by
  simp only [b9, b36, b50, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b51 : ambientAction F weylS (b51 F) =
    b40 F := by
  simp only [b40, b51, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b52 : ambientAction F weylS (b52 F) =
    b39 F := by
  simp only [b39, b52, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b53 : ambientAction F weylS (b53 F) =
    b38 F := by
  simp only [b38, b53, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b54 : ambientAction F weylS (b54 F) =
    b37 F := by
  simp only [b37, b54, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b55 : ambientAction F weylS (b55 F) =
    b46 F := by
  simp only [b46, b55, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b56 : ambientAction F weylS (b56 F) =
    b30 F + b45 F := by
  simp only [b30, b45, b56, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b57 : ambientAction F weylS (b57 F) =
    b48 F := by
  simp only [b48, b57, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b58 : ambientAction F weylS (b58 F) =
    b47 F := by
  simp only [b47, b58, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b59 : ambientAction F weylS (b59 F) =
    b30 F + b42 F := by
  simp only [b30, b42, b59, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b60 : ambientAction F weylS (b60 F) =
    b41 F := by
  simp only [b41, b60, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b61 : ambientAction F weylS (b61 F) =
    b44 F := by
  simp only [b44, b61, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b62 : ambientAction F weylS (b62 F) =
    b43 F := by
  simp only [b43, b62, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

theorem weylS_b63 : ambientAction F weylS (b63 F) =
    b49 F := by
  simp only [b49, b63, map_add, ambientAction_pure, weylS_e0, weylS_e1, weylS_e2, weylS_e3, weylS_e4, weylS_e5]
  all_goals simp only [pure, TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals refine (one_smul F _).symm.trans ?_
  all_goals match_scalars <;> ring_nf <;> simp [cast2 F, cast3 F, cast4 F, cast5 F, cast6 F, cast7 F, cast8 F]

/-- Preservation by the actual weylS elements, at every parameter. -/
theorem weylS_preserves :
    ∀ v ∈ sparseSpan F, ambientAction F weylS v ∈ sparseSpan F := by
  apply preserves_of_generators
  intro i
  fin_cases i
  · change ambientAction F weylS (b0 F) ∈ sparseSpan F
    rw [weylS_b0]
    exact (generator_mem F 4)
  · change ambientAction F weylS (b1 F) ∈ sparseSpan F
    rw [weylS_b1]
    exact (generator_mem F 8)
  · change ambientAction F weylS (b2 F) ∈ sparseSpan F
    rw [weylS_b2]
    exact (generator_mem F 6)
  · change ambientAction F weylS (b3 F) ∈ sparseSpan F
    rw [weylS_b3]
    exact (generator_mem F 11)
  · change ambientAction F weylS (b4 F) ∈ sparseSpan F
    rw [weylS_b4]
    exact (generator_mem F 0)
  · change ambientAction F weylS (b5 F) ∈ sparseSpan F
    rw [weylS_b5]
    exact (generator_mem F 7)
  · change ambientAction F weylS (b6 F) ∈ sparseSpan F
    rw [weylS_b6]
    exact (generator_mem F 2)
  · change ambientAction F weylS (b7 F) ∈ sparseSpan F
    rw [weylS_b7]
    exact (generator_mem F 5)
  · change ambientAction F weylS (b8 F) ∈ sparseSpan F
    rw [weylS_b8]
    exact (generator_mem F 1)
  · change ambientAction F weylS (b9 F) ∈ sparseSpan F
    rw [weylS_b9]
    exact (generator_mem F 10)
  · change ambientAction F weylS (b10 F) ∈ sparseSpan F
    rw [weylS_b10]
    exact (generator_mem F 9)
  · change ambientAction F weylS (b11 F) ∈ sparseSpan F
    rw [weylS_b11]
    exact (generator_mem F 3)
  · change ambientAction F weylS (b12 F) ∈ sparseSpan F
    rw [weylS_b12]
    exact ((sparseSpan F).add_mem (generator_mem F 7) (generator_mem F 23))
  · change ambientAction F weylS (b13 F) ∈ sparseSpan F
    rw [weylS_b13]
    exact (generator_mem F 27)
  · change ambientAction F weylS (b14 F) ∈ sparseSpan F
    rw [weylS_b14]
    exact (generator_mem F 26)
  · change ambientAction F weylS (b15 F) ∈ sparseSpan F
    rw [weylS_b15]
    exact (generator_mem F 25)
  · change ambientAction F weylS (b16 F) ∈ sparseSpan F
    rw [weylS_b16]
    exact (generator_mem F 24)
  · change ambientAction F weylS (b17 F) ∈ sparseSpan F
    rw [weylS_b17]
    exact (generator_mem F 33)
  · change ambientAction F weylS (b18 F) ∈ sparseSpan F
    rw [weylS_b18]
    exact (generator_mem F 32)
  · change ambientAction F weylS (b19 F) ∈ sparseSpan F
    rw [weylS_b19]
    exact (generator_mem F 35)
  · change ambientAction F weylS (b20 F) ∈ sparseSpan F
    rw [weylS_b20]
    exact (generator_mem F 29)
  · change ambientAction F weylS (b21 F) ∈ sparseSpan F
    rw [weylS_b21]
    exact (generator_mem F 28)
  · change ambientAction F weylS (b22 F) ∈ sparseSpan F
    rw [weylS_b22]
    exact (generator_mem F 31)
  · change ambientAction F weylS (b23 F) ∈ sparseSpan F
    rw [weylS_b23]
    exact ((sparseSpan F).add_mem (generator_mem F 5) (generator_mem F 12))
  · change ambientAction F weylS (b24 F) ∈ sparseSpan F
    rw [weylS_b24]
    exact (generator_mem F 16)
  · change ambientAction F weylS (b25 F) ∈ sparseSpan F
    rw [weylS_b25]
    exact (generator_mem F 15)
  · change ambientAction F weylS (b26 F) ∈ sparseSpan F
    rw [weylS_b26]
    exact (generator_mem F 14)
  · change ambientAction F weylS (b27 F) ∈ sparseSpan F
    rw [weylS_b27]
    exact (generator_mem F 13)
  · change ambientAction F weylS (b28 F) ∈ sparseSpan F
    rw [weylS_b28]
    exact (generator_mem F 21)
  · change ambientAction F weylS (b29 F) ∈ sparseSpan F
    rw [weylS_b29]
    exact (generator_mem F 20)
  · change ambientAction F weylS (b30 F) ∈ sparseSpan F
    rw [weylS_b30]
    exact (generator_mem F 34)
  · change ambientAction F weylS (b31 F) ∈ sparseSpan F
    rw [weylS_b31]
    exact (generator_mem F 22)
  · change ambientAction F weylS (b32 F) ∈ sparseSpan F
    rw [weylS_b32]
    exact (generator_mem F 18)
  · change ambientAction F weylS (b33 F) ∈ sparseSpan F
    rw [weylS_b33]
    exact (generator_mem F 17)
  · change ambientAction F weylS (b34 F) ∈ sparseSpan F
    rw [weylS_b34]
    exact (generator_mem F 30)
  · change ambientAction F weylS (b35 F) ∈ sparseSpan F
    rw [weylS_b35]
    exact (generator_mem F 19)
  · change ambientAction F weylS (b36 F) ∈ sparseSpan F
    rw [weylS_b36]
    exact ((sparseSpan F).add_mem (generator_mem F 10) (generator_mem F 50))
  · change ambientAction F weylS (b37 F) ∈ sparseSpan F
    rw [weylS_b37]
    exact (generator_mem F 54)
  · change ambientAction F weylS (b38 F) ∈ sparseSpan F
    rw [weylS_b38]
    exact (generator_mem F 53)
  · change ambientAction F weylS (b39 F) ∈ sparseSpan F
    rw [weylS_b39]
    exact (generator_mem F 52)
  · change ambientAction F weylS (b40 F) ∈ sparseSpan F
    rw [weylS_b40]
    exact (generator_mem F 51)
  · change ambientAction F weylS (b41 F) ∈ sparseSpan F
    rw [weylS_b41]
    exact (generator_mem F 60)
  · change ambientAction F weylS (b42 F) ∈ sparseSpan F
    rw [weylS_b42]
    exact ((sparseSpan F).add_mem (generator_mem F 34) (generator_mem F 59))
  · change ambientAction F weylS (b43 F) ∈ sparseSpan F
    rw [weylS_b43]
    exact (generator_mem F 62)
  · change ambientAction F weylS (b44 F) ∈ sparseSpan F
    rw [weylS_b44]
    exact (generator_mem F 61)
  · change ambientAction F weylS (b45 F) ∈ sparseSpan F
    rw [weylS_b45]
    exact ((sparseSpan F).add_mem (generator_mem F 34) (generator_mem F 56))
  · change ambientAction F weylS (b46 F) ∈ sparseSpan F
    rw [weylS_b46]
    exact (generator_mem F 55)
  · change ambientAction F weylS (b47 F) ∈ sparseSpan F
    rw [weylS_b47]
    exact (generator_mem F 58)
  · change ambientAction F weylS (b48 F) ∈ sparseSpan F
    rw [weylS_b48]
    exact (generator_mem F 57)
  · change ambientAction F weylS (b49 F) ∈ sparseSpan F
    rw [weylS_b49]
    exact (generator_mem F 63)
  · change ambientAction F weylS (b50 F) ∈ sparseSpan F
    rw [weylS_b50]
    exact ((sparseSpan F).add_mem (generator_mem F 9) (generator_mem F 36))
  · change ambientAction F weylS (b51 F) ∈ sparseSpan F
    rw [weylS_b51]
    exact (generator_mem F 40)
  · change ambientAction F weylS (b52 F) ∈ sparseSpan F
    rw [weylS_b52]
    exact (generator_mem F 39)
  · change ambientAction F weylS (b53 F) ∈ sparseSpan F
    rw [weylS_b53]
    exact (generator_mem F 38)
  · change ambientAction F weylS (b54 F) ∈ sparseSpan F
    rw [weylS_b54]
    exact (generator_mem F 37)
  · change ambientAction F weylS (b55 F) ∈ sparseSpan F
    rw [weylS_b55]
    exact (generator_mem F 46)
  · change ambientAction F weylS (b56 F) ∈ sparseSpan F
    rw [weylS_b56]
    exact ((sparseSpan F).add_mem (generator_mem F 30) (generator_mem F 45))
  · change ambientAction F weylS (b57 F) ∈ sparseSpan F
    rw [weylS_b57]
    exact (generator_mem F 48)
  · change ambientAction F weylS (b58 F) ∈ sparseSpan F
    rw [weylS_b58]
    exact (generator_mem F 47)
  · change ambientAction F weylS (b59 F) ∈ sparseSpan F
    rw [weylS_b59]
    exact ((sparseSpan F).add_mem (generator_mem F 30) (generator_mem F 42))
  · change ambientAction F weylS (b60 F) ∈ sparseSpan F
    rw [weylS_b60]
    exact (generator_mem F 41)
  · change ambientAction F weylS (b61 F) ∈ sparseSpan F
    rw [weylS_b61]
    exact (generator_mem F 44)
  · change ambientAction F weylS (b62 F) ∈ sparseSpan F
    rw [weylS_b62]
    exact (generator_mem F 43)
  · change ambientAction F weylS (b63 F) ∈ sparseSpan F
    rw [weylS_b63]
    exact (generator_mem F 49)

end Atlas.G2.Restricted.Steinberg.OrbitClosure
