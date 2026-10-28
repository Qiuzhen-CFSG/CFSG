module

public import Mathlib.Data.Finite.Perm
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
public import Theory.Mathieu.M11.Properties.Order

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- The four letters used by the bounded M11 centralizer word certificates. -/
@[expose]
public noncomputable def m11CentralizerWordGen : Fin 4 → M11
  | 0 => m11GeneratorAInM11
  | 1 => m11GeneratorBInM11
  | 2 => m11GeneratorAInM11⁻¹
  | _ => m11GeneratorBInM11⁻¹

/-- Evaluation of the short words used for the M11 involution centralizer. -/
@[expose]
public noncomputable def m11EvalCentralizerWord : List (Fin 4) → M11
  | [] => 1
  | i :: w => m11CentralizerWordGen i * m11EvalCentralizerWord w

/-- The eight-letter left chunk of the first centralizer generator. -/
@[expose]
public noncomputable def m11CentralizerWordLeft : M11 :=
  m11EvalCentralizerWord [1,0,1,1,0,1,1,0]

/-- Reflected point table for the eight-letter left chunk. -/
public theorem m11CentralizerWordLeft_perm :
    (m11CentralizerWordLeft : Equiv.Perm (Fin 11)) =
      List.formPerm [1,4,2,9,3,8,6,5] * Equiv.swap (7 : Fin 11) 11 := by
  ext x
  fin_cases x <;> rfl

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- The shared seven-letter chunk of the two M11 centralizer generators. -/
@[expose]
public noncomputable def m11CentralizerWordPivot : M11 :=
  m11EvalCentralizerWord [1,0,1,0,1,0,3]

/-- Reflected point table for the shared seven-letter chunk. -/
public theorem m11CentralizerWordPivot_perm :
    (m11CentralizerWordPivot : Equiv.Perm (Fin 11)) =
      List.formPerm [1,5,7] * Equiv.swap (2 : Fin 11) 11 *
        List.formPerm [3,8,10,6,9,4] := by
  ext x
  fin_cases x <;> rfl

/-- The seven-letter right chunk of the second centralizer generator. -/
@[expose]
public noncomputable def m11CentralizerWordRight : M11 :=
  m11EvalCentralizerWord [0,1,0,3,0,1,1]

/-- Reflected point table for the seven-letter right chunk. -/
public theorem m11CentralizerWordRight_perm :
    (m11CentralizerWordRight : Equiv.Perm (Fin 11)) =
      List.formPerm [1,4,8,3,10] * List.formPerm [2,5,9,6,7] := by
  ext x
  fin_cases x <;> rfl

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- An order-eight generator of the standard M11 involution centralizer. -/
@[expose]
public noncomputable def m11CentralizerU : M11 :=
  m11CentralizerWordLeft * m11CentralizerWordPivot

/-- Point table for the first centralizer generator. -/
public theorem m11CentralizerU_perm :
    (m11CentralizerU : Equiv.Perm (Fin 11)) =
      List.formPerm [2,7,4,8,10,5,11,9] * Equiv.swap (3 : Fin 11) 6 := by
  change (m11CentralizerWordLeft : Equiv.Perm (Fin 11)) *
      (m11CentralizerWordPivot : Equiv.Perm (Fin 11)) = _
  rw [m11CentralizerWordLeft_perm, m11CentralizerWordPivot_perm]
  ext x
  fin_cases x <;> rfl

/-- An order-three generator of the standard M11 involution centralizer. -/
@[expose]
public noncomputable def m11CentralizerV : M11 :=
  m11CentralizerWordPivot * m11CentralizerWordRight

/-- Point table for the second centralizer generator. -/
public theorem m11CentralizerV_perm :
    (m11CentralizerV : Equiv.Perm (Fin 11)) =
      List.formPerm [1,3,6] * List.formPerm [2,7,11] *
        List.formPerm [4,10,5] := by
  change (m11CentralizerWordPivot : Equiv.Perm (Fin 11)) *
      (m11CentralizerWordRight : Equiv.Perm (Fin 11)) = _
  rw [m11CentralizerWordPivot_perm, m11CentralizerWordRight_perm]
  ext x
  fin_cases x <;> rfl

/-- A nontrivial element fixing the points 1 and 2 in the generated centralizer. -/
@[expose]
public noncomputable def m11CentralizerW : M11 :=
  (m11CentralizerU * m11CentralizerV) ^ 2 * m11CentralizerU

/-- Point table for the terminal involution in the centralizer chain. -/
public theorem m11CentralizerW_perm :
    (m11CentralizerW : Equiv.Perm (Fin 11)) =
      Equiv.swap (3 : Fin 11) 6 * Equiv.swap (4 : Fin 11) 11 *
        Equiv.swap (5 : Fin 11) 9 * Equiv.swap (7 : Fin 11) 8 := by
  change (((m11CentralizerU : Equiv.Perm (Fin 11)) *
      (m11CentralizerV : Equiv.Perm (Fin 11))) ^ 2) *
      (m11CentralizerU : Equiv.Perm (Fin 11)) = _
  rw [m11CentralizerU_perm, m11CentralizerV_perm]
  ext x
  fin_cases x <;> rfl

/-- The centralizer in M11 of the standard involution. -/
@[expose]
public noncomputable def m11InvolutionCentralizer : Subgroup M11 :=
  Subgroup.centralizer ({m11GeneratorAInM11} : Set M11)

/-- The first short word centralizes the standard involution. -/
public theorem m11CentralizerU_mem :
    m11CentralizerU ∈ m11InvolutionCentralizer := by
  rw [m11InvolutionCentralizer, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  change (m11CentralizerU : Equiv.Perm (Fin 11)) *
      (m11GeneratorAInM11 : Equiv.Perm (Fin 11)) =
    (m11GeneratorAInM11 : Equiv.Perm (Fin 11)) *
      (m11CentralizerU : Equiv.Perm (Fin 11))
  rw [m11CentralizerU_perm]
  ext x
  fin_cases x <;> rfl

/-- The second short word centralizes the standard involution. -/
public theorem m11CentralizerV_mem :
    m11CentralizerV ∈ m11InvolutionCentralizer := by
  rw [m11InvolutionCentralizer, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  change (m11CentralizerV : Equiv.Perm (Fin 11)) *
      (m11GeneratorAInM11 : Equiv.Perm (Fin 11)) =
    (m11GeneratorAInM11 : Equiv.Perm (Fin 11)) *
      (m11CentralizerV : Equiv.Perm (Fin 11))
  rw [m11CentralizerV_perm]
  ext x
  fin_cases x <;> rfl

/-- The subgroup generated by the two short centralizer words. -/
@[expose]
public noncomputable def m11CentralizerWordSubgroup : Subgroup M11 :=
  Subgroup.closure ({m11CentralizerU, m11CentralizerV} : Set M11)



/-- The order-eight word belongs to the subgroup generated by the two words. -/
public theorem m11CentralizerU_mem_wordSubgroup :
    m11CentralizerU ∈ m11CentralizerWordSubgroup := by
  rw [m11CentralizerWordSubgroup]
  exact Subgroup.subset_closure (by simp)

/-- The order-three word belongs to the subgroup generated by the two words. -/
public theorem m11CentralizerV_mem_wordSubgroup :
    m11CentralizerV ∈ m11CentralizerWordSubgroup := by
  rw [m11CentralizerWordSubgroup]
  exact Subgroup.subset_closure (by simp)

/-- Membership in the standard involution centralizer is commutation
with the standard involution. -/
public theorem m11_mem_involutionCentralizer_iff (g : M11) :
    g ∈ m11InvolutionCentralizer ↔
      g * m11GeneratorAInM11 = m11GeneratorAInM11 * g := by
  rw [m11InvolutionCentralizer, Subgroup.mem_centralizer_singleton_iff]
/-- The generated subgroup is contained in the standard involution centralizer. -/
public theorem m11CentralizerWordSubgroup_le :
    m11CentralizerWordSubgroup ≤ m11InvolutionCentralizer := by
  rw [m11CentralizerWordSubgroup]
  apply (Subgroup.closure_le _).2
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact m11CentralizerU_mem
  · exact m11CentralizerV_mem

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


private theorem m11GeneratorA_apply (x : Fin 11) :
    m11GeneratorA x = ![4, 1, 10, 3, 11, 7, 6, 5, 9, 8, 2] x := by
  fin_cases x <;> rfl

private noncomputable def m11FixedPointEmbedding :
    Fin 3 ↪ Function.fixedPoints m11GeneratorA where
  toFun i :=
    ⟨![1, 3, 6] i, by
      fin_cases i <;> change m11GeneratorA _ = _ <;>
        rw [m11GeneratorA_apply] <;> rfl⟩
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private theorem m11FixedPointEmbedding_surjective :
    Function.Surjective m11FixedPointEmbedding := by
  rintro ⟨x, hx⟩
  change m11GeneratorA x = x at hx
  rw [m11GeneratorA_apply] at hx
  fin_cases x
  · simp at hx
  · exact ⟨0, by apply Subtype.ext; rfl⟩
  · simp at hx
  · exact ⟨1, by apply Subtype.ext; rfl⟩
  · simp at hx
  · simp at hx
  · exact ⟨2, by apply Subtype.ext; rfl⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · simp at hx

private noncomputable def m11FixedPointEquiv :
    Fin 3 ≃ Function.fixedPoints m11GeneratorA :=
  Equiv.ofBijective m11FixedPointEmbedding
    ⟨m11FixedPointEmbedding.injective, m11FixedPointEmbedding_surjective⟩

private noncomputable def m11MovedPointEmbedding :
    Fin 8 ↪ {x : Fin 11 // x ∈ m11GeneratorA.support} where
  toFun i :=
    ⟨![2, 4, 5, 7, 8, 9, 10, 11] i, by
      rw [Equiv.Perm.mem_support, m11GeneratorA_apply]
      fin_cases i <;> decide⟩
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private theorem m11MovedPointEmbedding_surjective :
    Function.Surjective m11MovedPointEmbedding := by
  rintro ⟨x, hx⟩
  rw [Equiv.Perm.mem_support, m11GeneratorA_apply] at hx
  fin_cases x
  · exact ⟨7, by apply Subtype.ext; rfl⟩
  · simp at hx
  · exact ⟨0, by apply Subtype.ext; rfl⟩
  · simp at hx
  · exact ⟨1, by apply Subtype.ext; rfl⟩
  · exact ⟨2, by apply Subtype.ext; rfl⟩
  · simp at hx
  · exact ⟨3, by apply Subtype.ext; rfl⟩
  · exact ⟨4, by apply Subtype.ext; rfl⟩
  · exact ⟨5, by apply Subtype.ext; rfl⟩
  · exact ⟨6, by apply Subtype.ext; rfl⟩

private noncomputable def m11MovedPointEquiv :
    Fin 8 ≃ {x : Fin 11 // x ∈ m11GeneratorA.support} :=
  Equiv.ofBijective m11MovedPointEmbedding
    ⟨m11MovedPointEmbedding.injective, m11MovedPointEmbedding_surjective⟩

private theorem m11Centralizer_ambient_mem
    (g : m11InvolutionCentralizer) :
    ((g : M11) : Equiv.Perm (Fin 11)) ∈
      Subgroup.centralizer ({m11GeneratorA} : Set (Equiv.Perm (Fin 11))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h :
      (g : M11) * m11GeneratorAInM11 =
        m11GeneratorAInM11 * (g : M11) :=
    (m11_mem_involutionCentralizer_iff (g : M11)).mp g.property
  exact congrArg (fun z : M11 => (z : Equiv.Perm (Fin 11))) h

private noncomputable def m11CentralizerFixedPerm
    (g : m11InvolutionCentralizer) :
    Equiv.Perm (Function.fixedPoints m11GeneratorA) :=
  ((g : M11) : Equiv.Perm (Fin 11)).subtypePerm fun _x =>
    Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer
      (m11Centralizer_ambient_mem g)

private theorem m11CentralizerFixedPerm_apply
    (g : m11InvolutionCentralizer)
    (x : Function.fixedPoints m11GeneratorA) :
    ((m11CentralizerFixedPerm g x :
      Function.fixedPoints m11GeneratorA) : Fin 11) =
      ((g : M11) : Equiv.Perm (Fin 11)) x := by
  simp [m11CentralizerFixedPerm, Equiv.Perm.subtypePerm_apply]

private noncomputable def m11CentralizerMovedImage
    (g : m11InvolutionCentralizer) :
    {x : Fin 11 // x ∈ m11GeneratorA.support} := by
  refine ⟨((g : M11) : Equiv.Perm (Fin 11)) 2, ?_⟩
  rw [Equiv.Perm.mem_support]
  intro hfixed
  have hiff :=
    Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer
      (m11Centralizer_ambient_mem g) (x := (2 : Fin 11))
  have hbaseFixed : (2 : Fin 11) ∈ Function.fixedPoints m11GeneratorA :=
    hiff.mp hfixed
  change m11GeneratorA 2 = 2 at hbaseFixed
  rw [m11GeneratorA_apply] at hbaseFixed
  simp at hbaseFixed

private noncomputable def m11CentralizerSignature
    (g : m11InvolutionCentralizer) :
    Equiv.Perm (Fin 3) × Fin 8 :=
  (m11FixedPointEquiv.symm.permCongrHom (m11CentralizerFixedPerm g),
    m11MovedPointEquiv.symm (m11CentralizerMovedImage g))

private theorem m11_eq_of_smul_embedding_eq
    (g h : M11) (x : Fin 4 ↪ Fin 11) (hgh : g • x = h • x) :
    g = h := by
  obtain ⟨a, ha⟩ := m11_fourPointOrbitMap_bijective.surjective x
  change a • m11FourPointBase = x at ha
  apply mul_right_cancel (b := a)
  apply m11_fourPointOrbitMap_bijective.injective
  calc
    (g * a) • m11FourPointBase = g • (a • m11FourPointBase) :=
      mul_smul g a m11FourPointBase
    _ = g • x := by rw [ha]
    _ = h • x := hgh
    _ = h • (a • m11FourPointBase) := by rw [ha]
    _ = (h * a) • m11FourPointBase := (mul_smul h a m11FourPointBase).symm

private theorem m11CentralizerSignature_injective :
    Function.Injective m11CentralizerSignature := by
  intro g h hsig
  have hfixed :
      m11CentralizerFixedPerm g = m11CentralizerFixedPerm h :=
    m11FixedPointEquiv.symm.permCongrHom.injective
      (congrArg Prod.fst hsig)
  have hmovedSubtype :
      m11CentralizerMovedImage g = m11CentralizerMovedImage h :=
    m11MovedPointEquiv.symm.injective (congrArg Prod.snd hsig)
  have hmoved :
      ((g : M11) : Equiv.Perm (Fin 11)) 2 =
        ((h : M11) : Equiv.Perm (Fin 11)) 2 :=
    congrArg Subtype.val hmovedSubtype
  have hfix
      (x : Function.fixedPoints m11GeneratorA) :
      ((g : M11) : Equiv.Perm (Fin 11)) x =
        ((h : M11) : Equiv.Perm (Fin 11)) x := by
    simpa only [m11CentralizerFixedPerm_apply] using
      congrArg (fun p : Equiv.Perm (Function.fixedPoints m11GeneratorA) =>
        ((p x : Function.fixedPoints m11GeneratorA) : Fin 11)) hfixed
  let source : Fin 4 ↪ Fin 11 := {
    toFun i := ![1, 3, 6, 2] i
    inj' := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    }
  have hsource : (g : M11) • source = (h : M11) • source := by
    ext i
    fin_cases i
    · change ((g : M11) • (1 : Fin 11)).val =
        ((h : M11) • (1 : Fin 11)).val
      exact congrArg Fin.val (hfix ⟨1, by
        change m11GeneratorA 1 = 1
        rw [m11GeneratorA_apply]
        rfl⟩)
    · change ((g : M11) • (3 : Fin 11)).val =
        ((h : M11) • (3 : Fin 11)).val
      exact congrArg Fin.val (hfix ⟨3, by
        change m11GeneratorA 3 = 3
        rw [m11GeneratorA_apply]
        rfl⟩)
    · change ((g : M11) • (6 : Fin 11)).val =
        ((h : M11) • (6 : Fin 11)).val
      exact congrArg Fin.val (hfix ⟨6, by
        change m11GeneratorA 6 = 6
        rw [m11GeneratorA_apply]
        rfl⟩)
    · change ((g : M11) • (2 : Fin 11)).val =
        ((h : M11) • (2 : Fin 11)).val
      exact congrArg Fin.val hmoved
  apply Subtype.ext
  exact m11_eq_of_smul_embedding_eq (g : M11) (h : M11) source hsource

/-- The centralizer of the standard involution in M11 has at most 48 elements. -/
public theorem m11_involutionCentralizer_card_le :
    Nat.card m11InvolutionCentralizer ≤ 48 := by
  have hcard := Nat.card_le_card_of_injective
    m11CentralizerSignature m11CentralizerSignature_injective
  norm_num [Nat.card_prod, Nat.card_perm, Nat.card_fin, Nat.factorial] at hcard ⊢
  exact hcard

private theorem m11CentralizerU_fixed_one :
    m11CentralizerU • (1 : Fin 11) = 1 := by
  change (m11CentralizerU : Equiv.Perm (Fin 11)) 1 = 1
  rw [m11CentralizerU_perm]
  rfl

private theorem m11CentralizerW_fixed_one :
    m11CentralizerW • (1 : Fin 11) = 1 := by
  change (m11CentralizerW : Equiv.Perm (Fin 11)) 1 = 1
  rw [m11CentralizerW_perm]
  rfl

private theorem m11CentralizerW_fixed_two :
    m11CentralizerW • (2 : Fin 11) = 2 := by
  change (m11CentralizerW : Equiv.Perm (Fin 11)) 2 = 2
  rw [m11CentralizerW_perm]
  rfl

private theorem m11CentralizerU_pow_fixed_one (n : Nat) :
    m11CentralizerU ^ n • (1 : Fin 11) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_smul, m11CentralizerU_fixed_one, ih]

private theorem m11CentralizerW_pow_fixed_one (n : Nat) :
    m11CentralizerW ^ n • (1 : Fin 11) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_smul, m11CentralizerW_fixed_one, ih]

private theorem m11CentralizerW_pow_fixed_two (n : Nat) :
    m11CentralizerW ^ n • (2 : Fin 11) = 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_smul, m11CentralizerW_fixed_two, ih]

private theorem m11CentralizerV_pow_one (i : Fin 3) :
    m11CentralizerV ^ (i : Nat) • (1 : Fin 11) = ![1, 3, 6] i := by
  fin_cases i
  · simp
  · change ((m11CentralizerV : Equiv.Perm (Fin 11)) ^ 1) 1 = 3
    rw [m11CentralizerV_perm]
    rfl
  · change ((m11CentralizerV : Equiv.Perm (Fin 11)) ^ 2) 1 = 6
    rw [m11CentralizerV_perm]
    rfl

private theorem m11CentralizerU_pow_two (i : Fin 8) :
    m11CentralizerU ^ (i : Nat) • (2 : Fin 11) =
      ![2, 7, 4, 8, 10, 5, 11, 9] i := by
  fin_cases i
  · simp
  · change ((m11CentralizerU : Equiv.Perm (Fin 11)) ^ 1) 2 = 7
    rw [m11CentralizerU_perm]
    rfl
  · change ((m11CentralizerU : Equiv.Perm (Fin 11)) ^ 2) 2 = 4
    rw [m11CentralizerU_perm]
    rfl
  · change ((m11CentralizerU : Equiv.Perm (Fin 11)) ^ 3) 2 = 8
    rw [m11CentralizerU_perm]
    rfl
  · change ((m11CentralizerU : Equiv.Perm (Fin 11)) ^ 4) 2 = 10
    rw [m11CentralizerU_perm]
    rfl
  · change ((m11CentralizerU : Equiv.Perm (Fin 11)) ^ 5) 2 = 5
    rw [m11CentralizerU_perm]
    rfl
  · change ((m11CentralizerU : Equiv.Perm (Fin 11)) ^ 6) 2 = 11
    rw [m11CentralizerU_perm]
    rfl
  · change ((m11CentralizerU : Equiv.Perm (Fin 11)) ^ 7) 2 = 9
    rw [m11CentralizerU_perm]
    rfl

private theorem m11CentralizerW_pow_three (i : Fin 2) :
    m11CentralizerW ^ (i : Nat) • (3 : Fin 11) = ![3, 6] i := by
  fin_cases i
  · simp
  · change ((m11CentralizerW : Equiv.Perm (Fin 11)) ^ 1) 3 = 6
    rw [m11CentralizerW_perm]
    rfl

private theorem m11CentralizerV_pow_one_injective :
    Function.Injective
      (fun i : Fin 3 => m11CentralizerV ^ (i : Nat) • (1 : Fin 11)) := by
  intro i j hij
  change m11CentralizerV ^ (i : Nat) • (1 : Fin 11) =
    m11CentralizerV ^ (j : Nat) • (1 : Fin 11) at hij
  rw [m11CentralizerV_pow_one, m11CentralizerV_pow_one] at hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem m11CentralizerU_pow_two_injective :
    Function.Injective
      (fun i : Fin 8 => m11CentralizerU ^ (i : Nat) • (2 : Fin 11)) := by
  intro i j hij
  change m11CentralizerU ^ (i : Nat) • (2 : Fin 11) =
    m11CentralizerU ^ (j : Nat) • (2 : Fin 11) at hij
  rw [m11CentralizerU_pow_two, m11CentralizerU_pow_two] at hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem m11CentralizerW_pow_three_injective :
    Function.Injective
      (fun i : Fin 2 => m11CentralizerW ^ (i : Nat) • (3 : Fin 11)) := by
  intro i j hij
  change m11CentralizerW ^ (i : Nat) • (3 : Fin 11) =
    m11CentralizerW ^ (j : Nat) • (3 : Fin 11) at hij
  rw [m11CentralizerW_pow_three, m11CentralizerW_pow_three] at hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem m11CentralizerW_mem_wordSubgroup :
    m11CentralizerW ∈ m11CentralizerWordSubgroup := by
  have hU : m11CentralizerU ∈ m11CentralizerWordSubgroup :=
    m11CentralizerU_mem_wordSubgroup
  have hV : m11CentralizerV ∈ m11CentralizerWordSubgroup :=
    m11CentralizerV_mem_wordSubgroup
  exact m11CentralizerWordSubgroup.mul_mem
    (m11CentralizerWordSubgroup.pow_mem
      (m11CentralizerWordSubgroup.mul_mem hU hV) 2) hU

private noncomputable def m11CentralizerNormalForm :
    Fin 3 × Fin 8 × Fin 2 → m11CentralizerWordSubgroup :=
  fun p =>
    ⟨m11CentralizerV ^ (p.1 : Nat) *
        (m11CentralizerU ^ (p.2.1 : Nat) *
          m11CentralizerW ^ (p.2.2 : Nat)),
      m11CentralizerWordSubgroup.mul_mem
        (m11CentralizerWordSubgroup.pow_mem
          m11CentralizerV_mem_wordSubgroup p.1)
        (m11CentralizerWordSubgroup.mul_mem
          (m11CentralizerWordSubgroup.pow_mem
            m11CentralizerU_mem_wordSubgroup p.2.1)
          (m11CentralizerWordSubgroup.pow_mem
            m11CentralizerW_mem_wordSubgroup p.2.2))⟩

private theorem m11CentralizerNormalForm_injective :
    Function.Injective m11CentralizerNormalForm := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ h
  have hval :
      m11CentralizerV ^ (i : Nat) *
          (m11CentralizerU ^ (j : Nat) * m11CentralizerW ^ (k : Nat)) =
        m11CentralizerV ^ (i' : Nat) *
          (m11CentralizerU ^ (j' : Nat) * m11CentralizerW ^ (k' : Nat)) := by
    simpa [m11CentralizerNormalForm] using congrArg
      (fun z : m11CentralizerWordSubgroup => (z : M11)) h
  have hi : i = i' := by
    apply m11CentralizerV_pow_one_injective
    have hpoint := congrArg (fun g : M11 => g • (1 : Fin 11)) hval
    simpa [mul_smul, m11CentralizerU_pow_fixed_one,
      m11CentralizerW_pow_fixed_one] using hpoint
  subst i'
  have htail :
      m11CentralizerU ^ (j : Nat) * m11CentralizerW ^ (k : Nat) =
        m11CentralizerU ^ (j' : Nat) * m11CentralizerW ^ (k' : Nat) :=
    mul_left_cancel hval
  have hj : j = j' := by
    apply m11CentralizerU_pow_two_injective
    have hpoint := congrArg (fun g : M11 => g • (2 : Fin 11)) htail
    simpa [mul_smul, m11CentralizerW_pow_fixed_two] using hpoint
  subst j'
  have hlast :
      m11CentralizerW ^ (k : Nat) = m11CentralizerW ^ (k' : Nat) :=
    mul_left_cancel htail
  have hk : k = k' := by
    apply m11CentralizerW_pow_three_injective
    exact congrArg (fun g : M11 => g • (3 : Fin 11)) hlast
  subst k'
  rfl

/-- The two short centralizer words generate a subgroup of order 48. -/
public theorem m11CentralizerWordSubgroup_card :
    Nat.card m11CentralizerWordSubgroup = 48 := by
  have hlower : 48 ≤ Nat.card m11CentralizerWordSubgroup := by
    have hcard := Nat.card_le_card_of_injective
      m11CentralizerNormalForm m11CentralizerNormalForm_injective
    norm_num [Nat.card_prod, Nat.card_fin] at hcard ⊢
    exact hcard
  have hupper :
      Nat.card m11CentralizerWordSubgroup ≤
        Nat.card m11InvolutionCentralizer :=
    Nat.card_le_card_of_injective
      (fun g : m11CentralizerWordSubgroup =>
        ⟨g.1, m11CentralizerWordSubgroup_le g.2⟩)
      (by
        intro g h hgh
        apply Subtype.ext
        exact congrArg
          (fun z : m11InvolutionCentralizer => (z : M11)) hgh)
  exact Nat.le_antisymm
    (hupper.trans m11_involutionCentralizer_card_le) hlower

/-- The short words generate the full involution centralizer. -/
public theorem m11_involutionCentralizer_eq_wordSubgroup :
    m11InvolutionCentralizer = m11CentralizerWordSubgroup :=
  (Subgroup.eq_of_le_of_card_ge m11CentralizerWordSubgroup_le
    (by
      rw [m11CentralizerWordSubgroup_card]
      exact m11_involutionCentralizer_card_le)).symm

/-- The centralizer of the standard involution in M11 has order 48. -/
public theorem m11_involutionCentralizer_card :
    Nat.card m11InvolutionCentralizer = 48 := by
  rw [m11_involutionCentralizer_eq_wordSubgroup,
    m11CentralizerWordSubgroup_card]

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open Matrix

public abbrev M11GL2Three := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)
private abbrev M11GL2Vector := Fin 2 → ZMod 3
private abbrev M11GL2NonzeroVector := {v : M11GL2Vector // v ≠ 0}
private abbrev M11MovedPoint := {x : Fin 11 // x ∈ m11GeneratorA.support}

private theorem m11GeneratorA_apply_gl2 (x : Fin 11) :
    m11GeneratorA x = ![4, 1, 10, 3, 11, 7, 6, 5, 9, 8, 2] x := by
  fin_cases x <;> rfl

private def m11MovedPointTable : Fin 8 → Fin 11 :=
  ![2, 7, 4, 8, 10, 5, 11, 9]

private noncomputable def m11MovedPointEmbedding2 : Fin 8 ↪ M11MovedPoint where
  toFun i :=
    ⟨![2, 7, 4, 8, 10, 5, 11, 9] i, by
      rw [Equiv.Perm.mem_support, m11GeneratorA_apply_gl2]
      fin_cases i <;> decide⟩
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private theorem m11MovedPointEmbedding22_surjective :
    Function.Surjective m11MovedPointEmbedding2 := by
  rintro ⟨x, hx⟩
  rw [Equiv.Perm.mem_support, m11GeneratorA_apply_gl2] at hx
  fin_cases x
  · exact ⟨6, by apply Subtype.ext; rfl⟩
  · simp at hx
  · exact ⟨0, by apply Subtype.ext; rfl⟩
  · simp at hx
  · exact ⟨2, by apply Subtype.ext; rfl⟩
  · exact ⟨5, by apply Subtype.ext; rfl⟩
  · simp at hx
  · exact ⟨1, by apply Subtype.ext; rfl⟩
  · exact ⟨3, by apply Subtype.ext; rfl⟩
  · exact ⟨7, by apply Subtype.ext; rfl⟩
  · exact ⟨4, by apply Subtype.ext; rfl⟩

private noncomputable def m11MovedPointEquiv2 : Fin 8 ≃ M11MovedPoint :=
  Equiv.ofBijective m11MovedPointEmbedding2
    ⟨m11MovedPointEmbedding2.injective, m11MovedPointEmbedding22_surjective⟩

private def m11MovedFourPointEmbedding : Fin 4 ↪ Fin 11 where
  toFun i := ![2, 7, 4, 8] i
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private def m11GL2VectorTable : Fin 8 → M11GL2Vector :=
  ![![0, 1], ![1, 1], ![1, 2], ![2, 0],
    ![0, 2], ![2, 2], ![2, 1], ![1, 0]]

private def m11GL2NonzeroVectorEmbedding : Fin 8 ↪ M11GL2NonzeroVector where
  toFun i := ⟨![![0, 1], ![1, 1], ![1, 2], ![2, 0],
    ![0, 2], ![2, 2], ![2, 1], ![1, 0]] i, by fin_cases i <;> decide⟩
  inj' := by
    decide

private theorem m11GL2NonzeroVectorEmbedding_surjective :
    Function.Surjective m11GL2NonzeroVectorEmbedding := by
  decide

private noncomputable def m11GL2NonzeroVectorEquiv : Fin 8 ≃ M11GL2NonzeroVector :=
  Equiv.ofBijective m11GL2NonzeroVectorEmbedding
    ⟨m11GL2NonzeroVectorEmbedding.injective,
      m11GL2NonzeroVectorEmbedding_surjective⟩

private theorem m11Centralizer_ambient_mem_gl2
    (g : m11InvolutionCentralizer) :
    ((g : M11) : Equiv.Perm (Fin 11)) ∈
      Subgroup.centralizer ({m11GeneratorA} : Set (Equiv.Perm (Fin 11))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := (m11_mem_involutionCentralizer_iff (g : M11)).mp g.property
  exact congrArg (fun z : M11 => (z : Equiv.Perm (Fin 11))) h

private noncomputable def m11CentralizerMovedPerm
    (g : m11InvolutionCentralizer) : Equiv.Perm M11MovedPoint :=
  ((g : M11) : Equiv.Perm (Fin 11)).subtypePerm fun x => by
    rw [Equiv.Perm.mem_support, Equiv.Perm.mem_support]
    exact not_congr (Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer
      (m11Centralizer_ambient_mem_gl2 g))

private theorem m11CentralizerMovedPerm_apply
    (g : m11InvolutionCentralizer) (x : M11MovedPoint) :
    ((m11CentralizerMovedPerm g x : M11MovedPoint) : Fin 11) =
      ((g : M11) : Equiv.Perm (Fin 11)) x := by
  simp [m11CentralizerMovedPerm, Equiv.Perm.subtypePerm_apply]

private noncomputable def m11CentralizerMovedPermHom :
    m11InvolutionCentralizer →* Equiv.Perm M11MovedPoint where
  toFun := m11CentralizerMovedPerm
  map_one' := by
    ext x
    simp [m11CentralizerMovedPerm, Equiv.Perm.subtypePerm_apply]
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    simp only [Equiv.Perm.mul_apply]
    rw [m11CentralizerMovedPerm_apply, m11CentralizerMovedPerm_apply,
      m11CentralizerMovedPerm_apply]
    simp [Subgroup.coe_mul, Equiv.Perm.mul_apply]

private noncomputable def m11CentralizerMovedFinPermHom :
    m11InvolutionCentralizer →* Equiv.Perm (Fin 8) :=
  m11MovedPointEquiv2.symm.permCongrHom.toMonoidHom.comp m11CentralizerMovedPermHom

private theorem m11CentralizerMovedFinPermHom_apply
    (g : m11InvolutionCentralizer) (i : Fin 8) :
    m11CentralizerMovedFinPermHom g i =
      m11MovedPointEquiv2.symm
        (m11CentralizerMovedPerm g (m11MovedPointEquiv2 i)) := by
  rfl
private def m11GL2U : M11GL2Three := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(0 : ZMod 3), 1; 1, 1] (by decide)

private def m11GL2V : M11GL2Three := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(1 : ZMod 3), 1; 0, 1] (by decide)

private def m11GL2VectorPerm (g : M11GL2Three) :
    Equiv.Perm M11GL2Vector :=
  (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.toEquiv

private def m11GL2NonzeroVectorPerm (g : M11GL2Three) :
    Equiv.Perm M11GL2NonzeroVector :=
  (m11GL2VectorPerm g).subtypePerm fun _ =>
    (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.map_ne_zero_iff

private noncomputable def m11GL2NonzeroVectorPermHom :
    M11GL2Three →* Equiv.Perm M11GL2NonzeroVector where
  toFun := m11GL2NonzeroVectorPerm
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    ext y
    simp [m11GL2NonzeroVectorPerm, m11GL2VectorPerm]
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    ext y
    simp only [m11GL2NonzeroVectorPerm, m11GL2VectorPerm]
    rw [Equiv.Perm.subtypePerm_mul]
    change (Matrix.GeneralLinearGroup.toLin (g * h)).toLinearEquiv.toEquiv (↑x) y =
      (((Matrix.GeneralLinearGroup.toLin g).toLinearEquiv.toEquiv *
        (Matrix.GeneralLinearGroup.toLin h).toLinearEquiv.toEquiv) (↑x)) y
    rw [show Matrix.GeneralLinearGroup.toLin (g * h) =
      Matrix.GeneralLinearGroup.toLin g * Matrix.GeneralLinearGroup.toLin h by
        exact (Matrix.GeneralLinearGroup.toLin).map_mul g h]
    rfl

private noncomputable def m11GL2FinPermHom :
    M11GL2Three →* Equiv.Perm (Fin 8) :=
  m11GL2NonzeroVectorEquiv.symm.permCongrHom.toMonoidHom.comp
    m11GL2NonzeroVectorPermHom

private theorem m11GL2FinPermHom_apply
    (g : M11GL2Three) (i : Fin 8) :
    m11GL2FinPermHom g i =
      m11GL2NonzeroVectorEquiv.symm
        (m11GL2NonzeroVectorPerm g (m11GL2NonzeroVectorEquiv i)) := by
  rfl
private noncomputable def m11CentralizerUInCentralizer : m11InvolutionCentralizer :=
  ⟨m11CentralizerU, m11CentralizerU_mem⟩

private noncomputable def m11CentralizerVInCentralizer : m11InvolutionCentralizer :=
  ⟨m11CentralizerV, m11CentralizerV_mem⟩

private def m11GL2UIndex : Fin 8 → Fin 8 :=
  ![1, 2, 3, 4, 5, 6, 7, 0]

private def m11GL2VIndex : Fin 8 → Fin 8 :=
  ![1, 6, 4, 3, 5, 2, 0, 7]

private theorem m11CentralizerU_movedPoint (i : Fin 8) :
    m11CentralizerMovedPerm m11CentralizerUInCentralizer
        (m11MovedPointEquiv2 i) =
      m11MovedPointEquiv2 (m11GL2UIndex i) := by
  apply Subtype.ext
  fin_cases i <;>
    simp [m11CentralizerMovedPerm_apply, m11MovedPointEquiv2,
      m11MovedPointEmbedding2, m11CentralizerUInCentralizer,
      m11GL2UIndex, m11CentralizerU_perm, Equiv.swap_apply_def]

private theorem m11GL2U_nonzeroVector (i : Fin 8) :
    m11GL2NonzeroVectorPerm m11GL2U (m11GL2NonzeroVectorEquiv i) =
      m11GL2NonzeroVectorEquiv (m11GL2UIndex i) := by
  apply Subtype.ext
  funext j
  fin_cases i <;> fin_cases j <;>
    decide

private theorem m11CentralizerV_movedPoint (i : Fin 8) :
    m11CentralizerMovedPerm m11CentralizerVInCentralizer
        (m11MovedPointEquiv2 i) =
      m11MovedPointEquiv2 (m11GL2VIndex i) := by
  apply Subtype.ext
  fin_cases i <;>
    simp [m11CentralizerMovedPerm_apply, m11MovedPointEquiv2,
      m11MovedPointEmbedding2, m11CentralizerVInCentralizer,
      m11GL2VIndex, m11CentralizerV_perm, Equiv.swap_apply_def]

private theorem m11GL2V_nonzeroVector (i : Fin 8) :
    m11GL2NonzeroVectorPerm m11GL2V (m11GL2NonzeroVectorEquiv i) =
      m11GL2NonzeroVectorEquiv (m11GL2VIndex i) := by
  apply Subtype.ext
  funext j
  fin_cases i <;> fin_cases j <;>
    decide

private theorem m11CentralizerU_action :
    m11CentralizerMovedFinPermHom m11CentralizerUInCentralizer =
      m11GL2FinPermHom m11GL2U := by
  ext i
  rw [m11CentralizerMovedFinPermHom_apply, m11GL2FinPermHom_apply]
  rw [m11CentralizerU_movedPoint, m11GL2U_nonzeroVector]
  simp

private theorem m11CentralizerV_action :
    m11CentralizerMovedFinPermHom m11CentralizerVInCentralizer =
      m11GL2FinPermHom m11GL2V := by
  ext i
  rw [m11CentralizerMovedFinPermHom_apply, m11GL2FinPermHom_apply]
  rw [m11CentralizerV_movedPoint, m11GL2V_nonzeroVector]
  simp

private theorem m11_eq_of_smul_embedding_eq_gl2
    (g h : M11) (x : Fin 4 ↪ Fin 11) (hgh : g • x = h • x) :
    g = h := by
  obtain ⟨a, ha⟩ := m11_fourPointOrbitMap_bijective.surjective x
  change a • m11FourPointBase = x at ha
  apply mul_right_cancel (b := a)
  apply m11_fourPointOrbitMap_bijective.injective
  calc
    (g * a) • m11FourPointBase = g • (a • m11FourPointBase) :=
      mul_smul g a m11FourPointBase
    _ = g • x := by rw [ha]
    _ = h • x := hgh
    _ = h • (a • m11FourPointBase) := by rw [ha]
    _ = (h * a) • m11FourPointBase := (mul_smul h a m11FourPointBase).symm

private theorem m11CentralizerMovedPermHom_injective :
    Function.Injective m11CentralizerMovedPermHom := by
  intro g h hgh
  apply Subtype.ext
  apply m11_eq_of_smul_embedding_eq_gl2
    (g : M11) (h : M11) m11MovedFourPointEmbedding
  have hpoint (i : Fin 8) :
      ((g : M11) : Equiv.Perm (Fin 11))
          (![2, 7, 4, 8, 10, 5, 11, 9] i) =
        ((h : M11) : Equiv.Perm (Fin 11))
          (![2, 7, 4, 8, 10, 5, 11, 9] i) := by
    have hi := congrArg
      (fun p : Equiv.Perm M11MovedPoint =>
        ((p (m11MovedPointEmbedding2 i) : M11MovedPoint) : Fin 11)) hgh
    simpa [m11CentralizerMovedPermHom, m11CentralizerMovedPerm_apply,
      m11MovedPointEmbedding2] using hi
  apply Function.Embedding.ext
  intro i
  fin_cases i
  · rw [Function.Embedding.smul_apply, Function.Embedding.smul_apply]
    change (g : M11) • (2 : Fin 11) = (h : M11) • (2 : Fin 11)
    have hp := hpoint 0
    change (g : M11) • (2 : Fin 11) = (h : M11) • (2 : Fin 11) at hp
    exact hp
  · rw [Function.Embedding.smul_apply, Function.Embedding.smul_apply]
    change (g : M11) • (7 : Fin 11) = (h : M11) • (7 : Fin 11)
    have hp := hpoint 1
    change (g : M11) • (7 : Fin 11) = (h : M11) • (7 : Fin 11) at hp
    exact hp
  · rw [Function.Embedding.smul_apply, Function.Embedding.smul_apply]
    change (g : M11) • (4 : Fin 11) = (h : M11) • (4 : Fin 11)
    have hp := hpoint 2
    change (g : M11) • (4 : Fin 11) = (h : M11) • (4 : Fin 11) at hp
    exact hp
  · rw [Function.Embedding.smul_apply, Function.Embedding.smul_apply]
    change (g : M11) • (8 : Fin 11) = (h : M11) • (8 : Fin 11)
    have hp := hpoint 3
    change (g : M11) • (8 : Fin 11) = (h : M11) • (8 : Fin 11) at hp
    exact hp

private theorem m11CentralizerMovedFinPermHom_injective :
    Function.Injective m11CentralizerMovedFinPermHom := by
  intro g h hgh
  apply m11CentralizerMovedPermHom_injective
  apply m11MovedPointEquiv2.symm.permCongrHom.injective
  simpa [m11CentralizerMovedFinPermHom] using hgh

private noncomputable def m11CentralizerGeneratorsSubgroup :
    Subgroup m11InvolutionCentralizer :=
  Subgroup.closure
    ({m11CentralizerUInCentralizer, m11CentralizerVInCentralizer} :
      Set m11InvolutionCentralizer)

private theorem m11CentralizerGeneratorsSubgroup_eq_top :
    m11CentralizerGeneratorsSubgroup = ⊤ := by
  have hmap :
      m11CentralizerGeneratorsSubgroup.map m11InvolutionCentralizer.subtype =
        m11InvolutionCentralizer := by
    rw [m11CentralizerGeneratorsSubgroup, MonoidHom.map_closure]
    simpa [m11CentralizerWordSubgroup, m11CentralizerUInCentralizer,
      m11CentralizerVInCentralizer, Set.image_insert_eq, Set.image_singleton] using
      m11_involutionCentralizer_eq_wordSubgroup.symm
  apply top_unique
  intro g hg
  have hg' : (g : M11) ∈
      m11CentralizerGeneratorsSubgroup.map m11InvolutionCentralizer.subtype := by
    rw [hmap]
    exact g.property
  rcases hg' with ⟨k, hk, hkg⟩
  have hkg' : k = g := Subtype.ext hkg
  simpa [hkg'] using hk

private theorem m11CentralizerFinPerm_range_le_gl2 :
    (m11CentralizerMovedFinPermHom).range ≤
      (m11GL2FinPermHom).range := by
  rw [MonoidHom.range_eq_map,
    ← m11CentralizerGeneratorsSubgroup_eq_top,
    m11CentralizerGeneratorsSubgroup,
    MonoidHom.map_closure]
  apply (Subgroup.closure_le _).2
  rintro x ⟨g, hg, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · rw [m11CentralizerU_action]
    exact ⟨m11GL2U, rfl⟩
  · rw [m11CentralizerV_action]
    exact ⟨m11GL2V, rfl⟩

private theorem m11CentralizerFinPerm_range_card :
    Nat.card (m11CentralizerMovedFinPermHom).range = 48 := by
  have hbij : Function.Bijective m11CentralizerMovedFinPermHom.rangeRestrict :=
    ⟨(MonoidHom.rangeRestrict_injective_iff).2
        m11CentralizerMovedFinPermHom_injective,
      MonoidHom.rangeRestrict_surjective _⟩
  calc
    Nat.card (m11CentralizerMovedFinPermHom).range =
        Nat.card m11InvolutionCentralizer :=
      (Nat.card_congr (Equiv.ofBijective
        m11CentralizerMovedFinPermHom.rangeRestrict hbij)).symm
    _ = 48 := m11_involutionCentralizer_card

private theorem m11GL2_card :
    Nat.card M11GL2Three = 48 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  change Nat.card (GL (Fin 2) (ZMod 3)) = 48
  have h := (Matrix.card_GL_field (n := 2) (𝔽 := ZMod 3))
  norm_num [Fin.prod_univ_two] at h ⊢
  exact h

private theorem m11GL2FinPerm_range_card_le :
    Nat.card (m11GL2FinPermHom).range ≤ 48 := by
  calc
    Nat.card (m11GL2FinPermHom).range ≤ Nat.card M11GL2Three :=
      Nat.card_le_card_of_surjective
        m11GL2FinPermHom.rangeRestrict
        (MonoidHom.rangeRestrict_surjective _)
    _ = 48 := m11GL2_card

private theorem m11FinPerm_ranges_eq :
    (m11CentralizerMovedFinPermHom).range =
      (m11GL2FinPermHom).range :=
  Subgroup.eq_of_le_of_card_ge m11CentralizerFinPerm_range_le_gl2
    (by
      rw [m11CentralizerFinPerm_range_card]
      exact m11GL2FinPerm_range_card_le)

private theorem m11GL2FinPermHom_injective :
    Function.Injective m11GL2FinPermHom := by
  have hcard :
      Nat.card M11GL2Three =
        Nat.card (m11GL2FinPermHom).range := by
    rw [← m11FinPerm_ranges_eq, m11CentralizerFinPerm_range_card,
      m11GL2_card]
  have hbij : Function.Bijective m11GL2FinPermHom.rangeRestrict :=
    (Nat.bijective_iff_surjective_and_card _).2
      ⟨MonoidHom.rangeRestrict_surjective _,
        hcard⟩
  exact (MonoidHom.rangeRestrict_injective_iff).mp hbij.1

private theorem m11CentralizerToGL_exists (g : m11InvolutionCentralizer) :
    ∃ h : M11GL2Three,
      m11GL2FinPermHom h = m11CentralizerMovedFinPermHom g := by
  have hg : m11CentralizerMovedFinPermHom g ∈
      (m11GL2FinPermHom).range := by
    rw [← m11FinPerm_ranges_eq]
    exact ⟨g, rfl⟩
  exact MonoidHom.mem_range.mp hg

private noncomputable def m11CentralizerToGLFun
    (g : m11InvolutionCentralizer) : M11GL2Three :=
  Classical.choose (m11CentralizerToGL_exists g)

private theorem m11CentralizerToGLFun_spec
    (g : m11InvolutionCentralizer) :
    m11GL2FinPermHom (m11CentralizerToGLFun g) =
      m11CentralizerMovedFinPermHom g :=
  Classical.choose_spec (m11CentralizerToGL_exists g)

public noncomputable def m11CentralizerToGL :
    m11InvolutionCentralizer →* M11GL2Three where
  toFun := m11CentralizerToGLFun
  map_one' := by
    apply m11GL2FinPermHom_injective
    calc
      m11GL2FinPermHom (m11CentralizerToGLFun 1) =
          m11CentralizerMovedFinPermHom 1 :=
        m11CentralizerToGLFun_spec 1
      _ = 1 := map_one m11CentralizerMovedFinPermHom
      _ = m11GL2FinPermHom 1 := (map_one m11GL2FinPermHom).symm
  map_mul' g h := by
    apply m11GL2FinPermHom_injective
    calc
      m11GL2FinPermHom (m11CentralizerToGLFun (g * h)) =
          m11CentralizerMovedFinPermHom (g * h) :=
        m11CentralizerToGLFun_spec (g * h)
      _ = m11CentralizerMovedFinPermHom g *
          m11CentralizerMovedFinPermHom h :=
        map_mul m11CentralizerMovedFinPermHom g h
      _ = m11GL2FinPermHom (m11CentralizerToGLFun g) *
          m11GL2FinPermHom (m11CentralizerToGLFun h) := by
        rw [m11CentralizerToGLFun_spec, m11CentralizerToGLFun_spec]
      _ = m11GL2FinPermHom
          (m11CentralizerToGLFun g * m11CentralizerToGLFun h) :=
        (map_mul m11GL2FinPermHom _ _).symm

private theorem m11CentralizerToGL_surjective :
    Function.Surjective m11CentralizerToGL := by
  intro h
  have hh : m11GL2FinPermHom h ∈
      (m11CentralizerMovedFinPermHom).range := by
    rw [m11FinPerm_ranges_eq]
    exact ⟨h, rfl⟩
  rcases MonoidHom.mem_range.mp hh with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  apply m11GL2FinPermHom_injective
  calc
    m11GL2FinPermHom (m11CentralizerToGL g) =
        m11CentralizerMovedFinPermHom g := by
      exact m11CentralizerToGLFun_spec g
    _ = m11GL2FinPermHom h := hg

public theorem m11CentralizerToGL_bijective :
    Function.Bijective m11CentralizerToGL := by
  apply (Nat.bijective_iff_surjective_and_card _).2
  refine ⟨m11CentralizerToGL_surjective, ?_⟩
  rw [m11_involutionCentralizer_card, m11GL2_card]

/-- The standard involution centralizer of M11 is isomorphic to GL₂(3). -/
@[expose] public noncomputable def m11InvolutionCentralizer_mulEquiv_gl2 :
    m11InvolutionCentralizer ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  MulEquiv.ofBijective m11CentralizerToGL m11CentralizerToGL_bijective

end Sporadic.Mathieu
