module

public import Theory.Representation.G2.RestrictedModules.Steinberg.OrbitClosure.Sparse

/-!
# Torus homogeneity of the sparse G₂ tensor generators

Each displayed sparse tensor has a single weight for the actual split torus.
These explicit character calculations prove preservation of the whole span.
Source: the concrete construction for GLS3 2.8.7 and 2.8.10(g).
-/

@[expose] public noncomputable section
namespace Atlas.G2.Restricted.Steinberg.OrbitClosure
open scoped TensorProduct
variable (F : Type*) [Field F] [CharP F 2]
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

theorem torus_e0 (l m : Fˣ) : NaturalCoordinates.action F (torus l m) (e F 0) =
    (l : F) • e F 0 := by
  ext k; fin_cases k <;> simp [NaturalCoordinates.action_torus, e]

theorem torus_e1 (l m : Fˣ) : NaturalCoordinates.action F (torus l m) (e F 1) =
    (m : F) • e F 1 := by
  ext k; fin_cases k <;> simp [NaturalCoordinates.action_torus, e]

theorem torus_e2 (l m : Fˣ) : NaturalCoordinates.action F (torus l m) (e F 2) =
    ((l * m⁻¹ : Fˣ) : F) • e F 2 := by
  ext k; fin_cases k <;> simp [NaturalCoordinates.action_torus, e]

theorem torus_e3 (l m : Fˣ) : NaturalCoordinates.action F (torus l m) (e F 3) =
    ((l⁻¹ * m : Fˣ) : F) • e F 3 := by
  ext k; fin_cases k <;> simp [NaturalCoordinates.action_torus, e]

theorem torus_e4 (l m : Fˣ) : NaturalCoordinates.action F (torus l m) (e F 4) =
    ((m⁻¹ : Fˣ) : F) • e F 4 := by
  ext k; fin_cases k <;> simp [NaturalCoordinates.action_torus, e]

theorem torus_e5 (l m : Fˣ) : NaturalCoordinates.action F (torus l m) (e F 5) =
    ((l⁻¹ : Fˣ) : F) • e F 5 := by
  ext k; fin_cases k <;> simp [NaturalCoordinates.action_torus, e]

theorem torus_b0 (l m : Fˣ) : ambientAction F (torus l m) (b0 F) =
    ((l : F)^2 * (m : F)) • b0 F := by
  simp only [b0, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b1 (l m : Fˣ) : ambientAction F (torus l m) (b1 F) =
    ((l : F)^3 * ((m : F)⁻¹)) • b1 F := by
  simp only [b1, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b2 (l m : Fˣ) : ambientAction F (torus l m) (b2 F) =
    ((l : F) * (m : F)) • b2 F := by
  simp only [b2, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b3 (l m : Fˣ) : ambientAction F (torus l m) (b3 F) =
    ((l : F)^2 * ((m : F)⁻¹)) • b3 F := by
  simp only [b3, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b4 (l m : Fˣ) : ambientAction F (torus l m) (b4 F) =
    ((l : F) * (m : F)^2) • b4 F := by
  simp only [b4, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b5 (l m : Fˣ) : ambientAction F (torus l m) (b5 F) =
    ((l : F)^2) • b5 F := by
  simp only [b5, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b6 (l m : Fˣ) : ambientAction F (torus l m) (b6 F) =
    ((l : F) * (m : F)) • b6 F := by
  simp only [b6, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b7 (l m : Fˣ) : ambientAction F (torus l m) (b7 F) =
    ((m : F)^2) • b7 F := by
  simp only [b7, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b8 (l m : Fˣ) : ambientAction F (torus l m) (b8 F) =
    (((l : F)⁻¹) * (m : F)^3) • b8 F := by
  simp only [b8, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b9 (l m : Fˣ) : ambientAction F (torus l m) (b9 F) =
    ((l : F)) • b9 F := by
  simp only [b9, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b10 (l m : Fˣ) : ambientAction F (torus l m) (b10 F) =
    ((m : F)) • b10 F := by
  simp only [b10, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b11 (l m : Fˣ) : ambientAction F (torus l m) (b11 F) =
    (((l : F)⁻¹) * (m : F)^2) • b11 F := by
  simp only [b11, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b12 (l m : Fˣ) : ambientAction F (torus l m) (b12 F) =
    ((l : F)^2) • b12 F := by
  simp only [b12, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b13 (l m : Fˣ) : ambientAction F (torus l m) (b13 F) =
    ((l : F)^3 * ((m : F)⁻¹)^2) • b13 F := by
  simp only [b13, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b14 (l m : Fˣ) : ambientAction F (torus l m) (b14 F) =
    ((l : F)^2 * ((m : F)⁻¹)) • b14 F := by
  simp only [b14, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b15 (l m : Fˣ) : ambientAction F (torus l m) (b15 F) =
    ((l : F)) • b15 F := by
  simp only [b15, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b16 (l m : Fˣ) : ambientAction F (torus l m) (b16 F) =
    ((m : F)) • b16 F := by
  simp only [b16, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b17 (l m : Fˣ) : ambientAction F (torus l m) (b17 F) =
    ((l : F)^2 * ((m : F)⁻¹)^2) • b17 F := by
  simp only [b17, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b18 (l m : Fˣ) : ambientAction F (torus l m) (b18 F) =
    ((l : F) * ((m : F)⁻¹)) • b18 F := by
  simp only [b18, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b19 (l m : Fˣ) : ambientAction F (torus l m) (b19 F) =
    ((l : F)^2 * ((m : F)⁻¹)^3) • b19 F := by
  simp only [b19, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b20 (l m : Fˣ) : ambientAction F (torus l m) (b20 F) =
    ((l : F) * ((m : F)⁻¹)) • b20 F := by
  simp only [b20, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b21 (l m : Fˣ) : ambientAction F (torus l m) (b21 F) =
    ((1 : F)) • b21 F := by
  simp only [b21, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b22 (l m : Fˣ) : ambientAction F (torus l m) (b22 F) =
    ((l : F) * ((m : F)⁻¹)^2) • b22 F := by
  simp only [b22, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b23 (l m : Fˣ) : ambientAction F (torus l m) (b23 F) =
    ((m : F)^2) • b23 F := by
  simp only [b23, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b24 (l m : Fˣ) : ambientAction F (torus l m) (b24 F) =
    ((l : F)) • b24 F := by
  simp only [b24, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b25 (l m : Fˣ) : ambientAction F (torus l m) (b25 F) =
    ((m : F)) • b25 F := by
  simp only [b25, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b26 (l m : Fˣ) : ambientAction F (torus l m) (b26 F) =
    (((l : F)⁻¹) * (m : F)^2) • b26 F := by
  simp only [b26, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b27 (l m : Fˣ) : ambientAction F (torus l m) (b27 F) =
    (((l : F)⁻¹)^2 * (m : F)^3) • b27 F := by
  simp only [b27, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b28 (l m : Fˣ) : ambientAction F (torus l m) (b28 F) =
    ((1 : F)) • b28 F := by
  simp only [b28, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b29 (l m : Fˣ) : ambientAction F (torus l m) (b29 F) =
    (((l : F)⁻¹) * (m : F)) • b29 F := by
  simp only [b29, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b30 (l m : Fˣ) : ambientAction F (torus l m) (b30 F) =
    (((m : F)⁻¹)) • b30 F := by
  simp only [b30, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b31 (l m : Fˣ) : ambientAction F (torus l m) (b31 F) =
    (((l : F)⁻¹)^2 * (m : F)) • b31 F := by
  simp only [b31, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b32 (l m : Fˣ) : ambientAction F (torus l m) (b32 F) =
    (((l : F)⁻¹) * (m : F)) • b32 F := by
  simp only [b32, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b33 (l m : Fˣ) : ambientAction F (torus l m) (b33 F) =
    (((l : F)⁻¹)^2 * (m : F)^2) • b33 F := by
  simp only [b33, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b34 (l m : Fˣ) : ambientAction F (torus l m) (b34 F) =
    (((l : F)⁻¹)) • b34 F := by
  simp only [b34, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b35 (l m : Fˣ) : ambientAction F (torus l m) (b35 F) =
    (((l : F)⁻¹)^3 * (m : F)^2) • b35 F := by
  simp only [b35, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b36 (l m : Fˣ) : ambientAction F (torus l m) (b36 F) =
    ((l : F)) • b36 F := by
  simp only [b36, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b37 (l m : Fˣ) : ambientAction F (torus l m) (b37 F) =
    ((l : F)^2 * ((m : F)⁻¹)^2) • b37 F := by
  simp only [b37, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b38 (l m : Fˣ) : ambientAction F (torus l m) (b38 F) =
    ((l : F) * ((m : F)⁻¹)) • b38 F := by
  simp only [b38, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b39 (l m : Fˣ) : ambientAction F (torus l m) (b39 F) =
    ((1 : F)) • b39 F := by
  simp only [b39, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b40 (l m : Fˣ) : ambientAction F (torus l m) (b40 F) =
    (((l : F)⁻¹) * (m : F)) • b40 F := by
  simp only [b40, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b41 (l m : Fˣ) : ambientAction F (torus l m) (b41 F) =
    ((l : F) * ((m : F)⁻¹)^2) • b41 F := by
  simp only [b41, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b42 (l m : Fˣ) : ambientAction F (torus l m) (b42 F) =
    (((m : F)⁻¹)) • b42 F := by
  simp only [b42, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b43 (l m : Fˣ) : ambientAction F (torus l m) (b43 F) =
    ((l : F) * ((m : F)⁻¹)^3) • b43 F := by
  simp only [b43, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b44 (l m : Fˣ) : ambientAction F (torus l m) (b44 F) =
    (((l : F)⁻¹) * ((m : F)⁻¹)) • b44 F := by
  simp only [b44, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b45 (l m : Fˣ) : ambientAction F (torus l m) (b45 F) =
    (((m : F)⁻¹)) • b45 F := by
  simp only [b45, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b46 (l m : Fˣ) : ambientAction F (torus l m) (b46 F) =
    (((l : F)⁻¹)) • b46 F := by
  simp only [b46, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b47 (l m : Fˣ) : ambientAction F (torus l m) (b47 F) =
    (((m : F)⁻¹)^2) • b47 F := by
  simp only [b47, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b48 (l m : Fˣ) : ambientAction F (torus l m) (b48 F) =
    (((l : F)⁻¹)^2) • b48 F := by
  simp only [b48, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b49 (l m : Fˣ) : ambientAction F (torus l m) (b49 F) =
    (((l : F)⁻¹) * ((m : F)⁻¹)^2) • b49 F := by
  simp only [b49, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b50 (l m : Fˣ) : ambientAction F (torus l m) (b50 F) =
    ((m : F)) • b50 F := by
  simp only [b50, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b51 (l m : Fˣ) : ambientAction F (torus l m) (b51 F) =
    ((l : F) * ((m : F)⁻¹)) • b51 F := by
  simp only [b51, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b52 (l m : Fˣ) : ambientAction F (torus l m) (b52 F) =
    ((1 : F)) • b52 F := by
  simp only [b52, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b53 (l m : Fˣ) : ambientAction F (torus l m) (b53 F) =
    (((l : F)⁻¹) * (m : F)) • b53 F := by
  simp only [b53, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b54 (l m : Fˣ) : ambientAction F (torus l m) (b54 F) =
    (((l : F)⁻¹)^2 * (m : F)^2) • b54 F := by
  simp only [b54, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b55 (l m : Fˣ) : ambientAction F (torus l m) (b55 F) =
    (((m : F)⁻¹)) • b55 F := by
  simp only [b55, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b56 (l m : Fˣ) : ambientAction F (torus l m) (b56 F) =
    (((l : F)⁻¹)) • b56 F := by
  simp only [b56, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b57 (l m : Fˣ) : ambientAction F (torus l m) (b57 F) =
    (((m : F)⁻¹)^2) • b57 F := by
  simp only [b57, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b58 (l m : Fˣ) : ambientAction F (torus l m) (b58 F) =
    (((l : F)⁻¹)^2) • b58 F := by
  simp only [b58, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b59 (l m : Fˣ) : ambientAction F (torus l m) (b59 F) =
    (((l : F)⁻¹)) • b59 F := by
  simp only [b59, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b60 (l m : Fˣ) : ambientAction F (torus l m) (b60 F) =
    (((l : F)⁻¹)^2 * (m : F)) • b60 F := by
  simp only [b60, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b61 (l m : Fˣ) : ambientAction F (torus l m) (b61 F) =
    (((l : F)⁻¹) * ((m : F)⁻¹)) • b61 F := by
  simp only [b61, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b62 (l m : Fˣ) : ambientAction F (torus l m) (b62 F) =
    (((l : F)⁻¹)^3 * (m : F)) • b62 F := by
  simp only [b62, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

theorem torus_b63 (l m : Fˣ) : ambientAction F (torus l m) (b63 F) =
    (((l : F)⁻¹)^2 * ((m : F)⁻¹)) • b63 F := by
  simp only [b63, map_add, ambientAction_pure, torus_e0, torus_e1, torus_e2, torus_e3, torus_e4, torus_e5]
  all_goals simp only [pure, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  all_goals match_scalars <;> (try simp only [Units.val_mul, Units.val_inv]) <;> field_simp <;> ring

/-- Every element of the actual split torus preserves the sparse span. -/
theorem torus_preserves (l m : Fˣ) :
    ∀ v ∈ sparseSpan F, ambientAction F (torus l m) v ∈ sparseSpan F := by
  apply preserves_of_generators
  intro i
  fin_cases i
  · change ambientAction F (torus l m) (b0 F) ∈ sparseSpan F
    rw [torus_b0]
    exact (sparseSpan F).smul_mem _ (generator_mem F 0)
  · change ambientAction F (torus l m) (b1 F) ∈ sparseSpan F
    rw [torus_b1]
    exact (sparseSpan F).smul_mem _ (generator_mem F 1)
  · change ambientAction F (torus l m) (b2 F) ∈ sparseSpan F
    rw [torus_b2]
    exact (sparseSpan F).smul_mem _ (generator_mem F 2)
  · change ambientAction F (torus l m) (b3 F) ∈ sparseSpan F
    rw [torus_b3]
    exact (sparseSpan F).smul_mem _ (generator_mem F 3)
  · change ambientAction F (torus l m) (b4 F) ∈ sparseSpan F
    rw [torus_b4]
    exact (sparseSpan F).smul_mem _ (generator_mem F 4)
  · change ambientAction F (torus l m) (b5 F) ∈ sparseSpan F
    rw [torus_b5]
    exact (sparseSpan F).smul_mem _ (generator_mem F 5)
  · change ambientAction F (torus l m) (b6 F) ∈ sparseSpan F
    rw [torus_b6]
    exact (sparseSpan F).smul_mem _ (generator_mem F 6)
  · change ambientAction F (torus l m) (b7 F) ∈ sparseSpan F
    rw [torus_b7]
    exact (sparseSpan F).smul_mem _ (generator_mem F 7)
  · change ambientAction F (torus l m) (b8 F) ∈ sparseSpan F
    rw [torus_b8]
    exact (sparseSpan F).smul_mem _ (generator_mem F 8)
  · change ambientAction F (torus l m) (b9 F) ∈ sparseSpan F
    rw [torus_b9]
    exact (sparseSpan F).smul_mem _ (generator_mem F 9)
  · change ambientAction F (torus l m) (b10 F) ∈ sparseSpan F
    rw [torus_b10]
    exact (sparseSpan F).smul_mem _ (generator_mem F 10)
  · change ambientAction F (torus l m) (b11 F) ∈ sparseSpan F
    rw [torus_b11]
    exact (sparseSpan F).smul_mem _ (generator_mem F 11)
  · change ambientAction F (torus l m) (b12 F) ∈ sparseSpan F
    rw [torus_b12]
    exact (sparseSpan F).smul_mem _ (generator_mem F 12)
  · change ambientAction F (torus l m) (b13 F) ∈ sparseSpan F
    rw [torus_b13]
    exact (sparseSpan F).smul_mem _ (generator_mem F 13)
  · change ambientAction F (torus l m) (b14 F) ∈ sparseSpan F
    rw [torus_b14]
    exact (sparseSpan F).smul_mem _ (generator_mem F 14)
  · change ambientAction F (torus l m) (b15 F) ∈ sparseSpan F
    rw [torus_b15]
    exact (sparseSpan F).smul_mem _ (generator_mem F 15)
  · change ambientAction F (torus l m) (b16 F) ∈ sparseSpan F
    rw [torus_b16]
    exact (sparseSpan F).smul_mem _ (generator_mem F 16)
  · change ambientAction F (torus l m) (b17 F) ∈ sparseSpan F
    rw [torus_b17]
    exact (sparseSpan F).smul_mem _ (generator_mem F 17)
  · change ambientAction F (torus l m) (b18 F) ∈ sparseSpan F
    rw [torus_b18]
    exact (sparseSpan F).smul_mem _ (generator_mem F 18)
  · change ambientAction F (torus l m) (b19 F) ∈ sparseSpan F
    rw [torus_b19]
    exact (sparseSpan F).smul_mem _ (generator_mem F 19)
  · change ambientAction F (torus l m) (b20 F) ∈ sparseSpan F
    rw [torus_b20]
    exact (sparseSpan F).smul_mem _ (generator_mem F 20)
  · change ambientAction F (torus l m) (b21 F) ∈ sparseSpan F
    rw [torus_b21]
    exact (sparseSpan F).smul_mem _ (generator_mem F 21)
  · change ambientAction F (torus l m) (b22 F) ∈ sparseSpan F
    rw [torus_b22]
    exact (sparseSpan F).smul_mem _ (generator_mem F 22)
  · change ambientAction F (torus l m) (b23 F) ∈ sparseSpan F
    rw [torus_b23]
    exact (sparseSpan F).smul_mem _ (generator_mem F 23)
  · change ambientAction F (torus l m) (b24 F) ∈ sparseSpan F
    rw [torus_b24]
    exact (sparseSpan F).smul_mem _ (generator_mem F 24)
  · change ambientAction F (torus l m) (b25 F) ∈ sparseSpan F
    rw [torus_b25]
    exact (sparseSpan F).smul_mem _ (generator_mem F 25)
  · change ambientAction F (torus l m) (b26 F) ∈ sparseSpan F
    rw [torus_b26]
    exact (sparseSpan F).smul_mem _ (generator_mem F 26)
  · change ambientAction F (torus l m) (b27 F) ∈ sparseSpan F
    rw [torus_b27]
    exact (sparseSpan F).smul_mem _ (generator_mem F 27)
  · change ambientAction F (torus l m) (b28 F) ∈ sparseSpan F
    rw [torus_b28]
    exact (sparseSpan F).smul_mem _ (generator_mem F 28)
  · change ambientAction F (torus l m) (b29 F) ∈ sparseSpan F
    rw [torus_b29]
    exact (sparseSpan F).smul_mem _ (generator_mem F 29)
  · change ambientAction F (torus l m) (b30 F) ∈ sparseSpan F
    rw [torus_b30]
    exact (sparseSpan F).smul_mem _ (generator_mem F 30)
  · change ambientAction F (torus l m) (b31 F) ∈ sparseSpan F
    rw [torus_b31]
    exact (sparseSpan F).smul_mem _ (generator_mem F 31)
  · change ambientAction F (torus l m) (b32 F) ∈ sparseSpan F
    rw [torus_b32]
    exact (sparseSpan F).smul_mem _ (generator_mem F 32)
  · change ambientAction F (torus l m) (b33 F) ∈ sparseSpan F
    rw [torus_b33]
    exact (sparseSpan F).smul_mem _ (generator_mem F 33)
  · change ambientAction F (torus l m) (b34 F) ∈ sparseSpan F
    rw [torus_b34]
    exact (sparseSpan F).smul_mem _ (generator_mem F 34)
  · change ambientAction F (torus l m) (b35 F) ∈ sparseSpan F
    rw [torus_b35]
    exact (sparseSpan F).smul_mem _ (generator_mem F 35)
  · change ambientAction F (torus l m) (b36 F) ∈ sparseSpan F
    rw [torus_b36]
    exact (sparseSpan F).smul_mem _ (generator_mem F 36)
  · change ambientAction F (torus l m) (b37 F) ∈ sparseSpan F
    rw [torus_b37]
    exact (sparseSpan F).smul_mem _ (generator_mem F 37)
  · change ambientAction F (torus l m) (b38 F) ∈ sparseSpan F
    rw [torus_b38]
    exact (sparseSpan F).smul_mem _ (generator_mem F 38)
  · change ambientAction F (torus l m) (b39 F) ∈ sparseSpan F
    rw [torus_b39]
    exact (sparseSpan F).smul_mem _ (generator_mem F 39)
  · change ambientAction F (torus l m) (b40 F) ∈ sparseSpan F
    rw [torus_b40]
    exact (sparseSpan F).smul_mem _ (generator_mem F 40)
  · change ambientAction F (torus l m) (b41 F) ∈ sparseSpan F
    rw [torus_b41]
    exact (sparseSpan F).smul_mem _ (generator_mem F 41)
  · change ambientAction F (torus l m) (b42 F) ∈ sparseSpan F
    rw [torus_b42]
    exact (sparseSpan F).smul_mem _ (generator_mem F 42)
  · change ambientAction F (torus l m) (b43 F) ∈ sparseSpan F
    rw [torus_b43]
    exact (sparseSpan F).smul_mem _ (generator_mem F 43)
  · change ambientAction F (torus l m) (b44 F) ∈ sparseSpan F
    rw [torus_b44]
    exact (sparseSpan F).smul_mem _ (generator_mem F 44)
  · change ambientAction F (torus l m) (b45 F) ∈ sparseSpan F
    rw [torus_b45]
    exact (sparseSpan F).smul_mem _ (generator_mem F 45)
  · change ambientAction F (torus l m) (b46 F) ∈ sparseSpan F
    rw [torus_b46]
    exact (sparseSpan F).smul_mem _ (generator_mem F 46)
  · change ambientAction F (torus l m) (b47 F) ∈ sparseSpan F
    rw [torus_b47]
    exact (sparseSpan F).smul_mem _ (generator_mem F 47)
  · change ambientAction F (torus l m) (b48 F) ∈ sparseSpan F
    rw [torus_b48]
    exact (sparseSpan F).smul_mem _ (generator_mem F 48)
  · change ambientAction F (torus l m) (b49 F) ∈ sparseSpan F
    rw [torus_b49]
    exact (sparseSpan F).smul_mem _ (generator_mem F 49)
  · change ambientAction F (torus l m) (b50 F) ∈ sparseSpan F
    rw [torus_b50]
    exact (sparseSpan F).smul_mem _ (generator_mem F 50)
  · change ambientAction F (torus l m) (b51 F) ∈ sparseSpan F
    rw [torus_b51]
    exact (sparseSpan F).smul_mem _ (generator_mem F 51)
  · change ambientAction F (torus l m) (b52 F) ∈ sparseSpan F
    rw [torus_b52]
    exact (sparseSpan F).smul_mem _ (generator_mem F 52)
  · change ambientAction F (torus l m) (b53 F) ∈ sparseSpan F
    rw [torus_b53]
    exact (sparseSpan F).smul_mem _ (generator_mem F 53)
  · change ambientAction F (torus l m) (b54 F) ∈ sparseSpan F
    rw [torus_b54]
    exact (sparseSpan F).smul_mem _ (generator_mem F 54)
  · change ambientAction F (torus l m) (b55 F) ∈ sparseSpan F
    rw [torus_b55]
    exact (sparseSpan F).smul_mem _ (generator_mem F 55)
  · change ambientAction F (torus l m) (b56 F) ∈ sparseSpan F
    rw [torus_b56]
    exact (sparseSpan F).smul_mem _ (generator_mem F 56)
  · change ambientAction F (torus l m) (b57 F) ∈ sparseSpan F
    rw [torus_b57]
    exact (sparseSpan F).smul_mem _ (generator_mem F 57)
  · change ambientAction F (torus l m) (b58 F) ∈ sparseSpan F
    rw [torus_b58]
    exact (sparseSpan F).smul_mem _ (generator_mem F 58)
  · change ambientAction F (torus l m) (b59 F) ∈ sparseSpan F
    rw [torus_b59]
    exact (sparseSpan F).smul_mem _ (generator_mem F 59)
  · change ambientAction F (torus l m) (b60 F) ∈ sparseSpan F
    rw [torus_b60]
    exact (sparseSpan F).smul_mem _ (generator_mem F 60)
  · change ambientAction F (torus l m) (b61 F) ∈ sparseSpan F
    rw [torus_b61]
    exact (sparseSpan F).smul_mem _ (generator_mem F 61)
  · change ambientAction F (torus l m) (b62 F) ∈ sparseSpan F
    rw [torus_b62]
    exact (sparseSpan F).smul_mem _ (generator_mem F 62)
  · change ambientAction F (torus l m) (b63 F) ∈ sparseSpan F
    rw [torus_b63]
    exact (sparseSpan F).smul_mem _ (generator_mem F 63)

end Atlas.G2.Restricted.Steinberg.OrbitClosure
