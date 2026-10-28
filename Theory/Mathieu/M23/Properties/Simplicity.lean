module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Tactic.FinCases
public import Theory.Mathieu.M22.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.Index
public import Theory.Mathieu.M22.Properties.Order
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Theory.Mathieu.M22.Properties.Simplicity
public import Theory.Mathieu.M23.Generators
public import Theory.Mathieu.M23.Block
public import Theory.Mathieu.M23.Basic
public import Theory.Mathieu.M23.Properties.PointStabilizer
public import Theory.GroupAction.Stabilizer
public import Theory.GroupTheory.Simple

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/-- The GLS/Atlas relabelling from the degree-22 M22 action to the complement of point 9
in the natural degree-23 M23 action. -/
@[expose] public def m22M23PointMap : Fin 22 → Fin 23 :=
  ![5, 18, 7, 3, 2, 17, 22, 8, 16, 14, 23, 21, 13, 4, 20, 15, 10, 6, 11, 12, 1, 19]

/-- A left inverse used to prove that the relabelling is injective.  Its value at the
omitted point 9 is irrelevant. -/
@[expose] public def m22M23PointMapLeftInverse : Fin 23 → Fin 22 :=
  ![10, 20, 4, 3, 13, 22, 17, 2, 7, 1, 16, 18, 19, 12, 9, 15, 8, 5, 1, 21, 14, 11, 6]

public theorem m22M23PointMap_leftInverse :
    Function.LeftInverse m22M23PointMapLeftInverse m22M23PointMap := by
  decide +kernel

public theorem m22M23PointMap_injective : Function.Injective m22M23PointMap :=
  m22M23PointMap_leftInverse.injective

public theorem m22M23PointMap_ne_nine (i : Fin 22) : m22M23PointMap i ≠ (9 : Fin 23) := by
  revert i
  decide +kernel

@[expose] public def m22M23PointEmbedding : Fin 22 ↪ Fin 23 :=
  ⟨m22M23PointMap, m22M23PointMap_injective⟩

/-- Relabel a degree-22 permutation and extend it by fixing point 9. -/
@[expose] public noncomputable def m22M23RelabelHom :
    Equiv.Perm (Fin 22) →* Equiv.Perm (Fin 23) :=
  Equiv.Perm.viaEmbeddingHom m22M23PointEmbedding

/-- Lower half of the degree-23 point set, used by finite relabelling checks. -/
@[expose] public def m23M22LowIndex (i : Fin 12) : Fin 23 :=
  ⟨i.val, i.isLt.trans (by decide +kernel)⟩

/-- Upper half of the degree-23 point set, used by finite relabelling checks. -/
@[expose] public def m23M22HighIndex (i : Fin 11) : Fin 23 :=
  ⟨12 + i.val, by omega⟩

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/-- Direct point table for the first relabelled M22 generator. -/
@[expose] public def m23M22GeneratorATable : Fin 23 → Fin 23 :=
  ![14, 1, 13, 10, 18, 22, 8, 16, 6, 9, 3, 11, 12, 2, 23, 15, 7, 17, 4, 19, 21, 20, 5]

public theorem m23M22GeneratorATable_involutive :
    Function.Involutive m23M22GeneratorATable := by
  intro i
  revert i
  decide +kernel

/-- The first relabelled M22 generator, implemented by direct table lookup. -/
@[expose] public def m23M22GeneratorA : Equiv.Perm (Fin 23) where
  toFun := m23M22GeneratorATable
  invFun := m23M22GeneratorATable
  left_inv := m23M22GeneratorATable_involutive
  right_inv := m23M22GeneratorATable_involutive

public theorem m23M22GeneratorA_fix9 : m23M22GeneratorA (9 : Fin 23) = 9 := rfl

/-- Direct point table for the second relabelled M22 generator. -/
@[expose] public def m23M22GeneratorBTable : Fin 23 → Fin 23 :=
  ![16, 23, 4, 19, 7, 3, 12, 11, 15, 9, 10, 2, 6, 17, 14, 22, 20, 13, 5, 18, 1, 8, 21]

/-- Inverse point table for the second relabelled M22 generator. -/
@[expose] public def m23M22GeneratorBInvTable : Fin 23 → Fin 23 :=
  ![1, 20, 11, 5, 2, 18, 12, 4, 21, 9, 10, 7, 6, 17, 14, 8, 23, 13, 19, 3, 16, 22, 15]

public theorem m23M22GeneratorB_leftInverse (i : Fin 23) :
    m23M22GeneratorBInvTable (m23M22GeneratorBTable i) = i := by
  revert i
  decide +kernel

public theorem m23M22GeneratorB_rightInverse (i : Fin 23) :
    m23M22GeneratorBTable (m23M22GeneratorBInvTable i) = i := by
  revert i
  decide +kernel

/-- The second relabelled M22 generator, implemented by direct table lookup. -/
@[expose] public def m23M22GeneratorB : Equiv.Perm (Fin 23) where
  toFun := m23M22GeneratorBTable
  invFun := m23M22GeneratorBInvTable
  left_inv := m23M22GeneratorB_leftInverse
  right_inv := m23M22GeneratorB_rightInverse

public theorem m23M22GeneratorB_fix9 : m23M22GeneratorB (9 : Fin 23) = 9 := rfl

open scoped Pointwise

set_option maxRecDepth 100000
set_option maxHeartbeats 800000
public def m23M22GeneratorABlockIndex : Fin 253 → Fin 253 :=
  ![74,68,75,5,26,3,40,59,72,60,23,11,66,43,54,15,34,49,30,19,47,65,63,10,24,39,4,57,76,29,18,50,45,33,16,56,44,70,73,25,6,41,53,13,36,32,46,20,52,17,31,51,48,42,14,55,35,27,69,7,9,61,64,22,62,21,12,67,1,58,37,71,8,38,0,2,28,204,131,189,172,121,215,158,199,142,244,224,228,89,179,112,239,195,163,118,219,241,234,231,137,150,107,249,104,242,148,102,251,229,173,235,91,125,209,153,116,183,95,167,184,81,169,217,191,113,206,197,128,211,162,78,135,165,187,132,212,100,246,248,151,227,85,238,180,245,226,240,106,247,101,140,152,115,214,181,208,193,83,160,159,161,130,94,200,133,186,119,202,122,216,171,80,110,221,250,232,177,237,90,144,155,196,117,120,213,166,134,201,79,190,124,220,157,205,93,182,127,198,84,164,188,168,203,77,194,126,210,156,114,207,129,136,185,154,82,170,123,218,96,192,174,222,243,87,225,146,141,88,109,233,99,176,230,98,111,236,178,143,92,147,97,105,223,86,145,138,149,139,103,175,108,252]

private theorem m23M22GeneratorA_block_bits (i : Fin 253) (x : Fin 23) :
    (m23BlockMask i).testBit (m23M22GeneratorA.symm x).val =
      (m23BlockMask (m23M22GeneratorABlockIndex i)).testBit x.val := by
  revert i x
  decide +kernel

/-- Direct bit-level action of the first relabelled M22 generator on all heptads. -/
public theorem m23M22GeneratorA_blockAt (i : Fin 253) :
    m23M22GeneratorA • m23BlockAt i =
      m23BlockAt (m23M22GeneratorABlockIndex i) :=
  m23Perm_smul_blockAt_of_bits _ _ _ (m23M22GeneratorA_block_bits i)

private theorem m23M22GeneratorABlockIndex_injective :
    Function.Injective m23M22GeneratorABlockIndex := by
  intro i j hij
  apply m23BlockAt_injective
  apply (MulAction.injective m23M22GeneratorA :
    Function.Injective
      (fun B : Finset (Fin 23) => m23M22GeneratorA • B))
  change m23M22GeneratorA • m23BlockAt i =
    m23M22GeneratorA • m23BlockAt j
  rw [m23M22GeneratorA_blockAt i, m23M22GeneratorA_blockAt j, hij]

private theorem m23M22GeneratorABlockIndex_surjective :
    Function.Surjective m23M22GeneratorABlockIndex :=
  Finite.surjective_of_injective m23M22GeneratorABlockIndex_injective

public theorem m23M22GeneratorA_blocks_smul :
    m23M22GeneratorA • m23Blocks = m23Blocks :=
  m23Blocks_smul_of_reindex
    m23M22GeneratorA m23M22GeneratorABlockIndex
    m23M22GeneratorABlockIndex_surjective
    m23M22GeneratorA_blockAt

public theorem m23M22GeneratorA_mem_M23 : m23M22GeneratorA ∈ M23 := by
  rw [mem_M23_iff]
  have h := congrArg
    (fun s : Finset (Finset (Fin 23)) => (s : Set (Finset (Fin 23))))
    m23M22GeneratorA_blocks_smul
  simpa only [Finset.coe_smul_finset] using h
public def m23M22GeneratorBBlockIndex : Fin 253 → Fin 253 :=
  ![78,198,42,176,200,44,175,182,188,143,133,144,22,96,183,197,100,8,199,98,40,233,67,223,212,28,171,170,155,119,251,249,111,68,20,126,206,154,32,160,147,211,124,123,224,122,9,234,66,88,172,86,148,84,30,169,4,247,19,205,252,70,62,214,225,56,69,250,248,125,207,118,55,213,112,226,63,192,190,38,181,138,141,24,136,179,7,103,184,101,93,47,195,134,140,139,21,97,191,43,94,189,99,6,173,23,80,0,137,77,135,79,142,194,46,193,104,37,178,187,177,186,45,102,174,48,196,95,41,185,5,180,39,161,145,31,164,108,59,235,16,120,239,114,209,90,167,34,92,1,150,83,158,71,230,220,128,203,246,76,245,227,116,218,53,216,11,232,61,243,73,131,50,162,2,87,163,82,153,85,26,238,51,222,237,64,121,202,236,208,107,58,221,57,113,52,210,15,201,240,65,149,29,157,152,81,36,168,89,166,35,156,151,27,159,33,165,91,3,146,25,109,229,241,130,129,75,10,228,14,117,54,219,13,217,127,17,49,106,74,244,105,242,72,18,132,204,115,215,110,12,231,60]

private theorem m23M22GeneratorB_block_bits (i : Fin 253) (x : Fin 23) :
    (m23BlockMask i).testBit (m23M22GeneratorB.symm x).val =
      (m23BlockMask (m23M22GeneratorBBlockIndex i)).testBit x.val := by
  revert i x
  decide +kernel

/-- Direct bit-level action of the second relabelled M22 generator on all heptads. -/
public theorem m23M22GeneratorB_blockAt (i : Fin 253) :
    m23M22GeneratorB • m23BlockAt i =
      m23BlockAt (m23M22GeneratorBBlockIndex i) :=
  m23Perm_smul_blockAt_of_bits _ _ _ (m23M22GeneratorB_block_bits i)

private theorem m23M22GeneratorBBlockIndex_injective :
    Function.Injective m23M22GeneratorBBlockIndex := by
  intro i j hij
  apply m23BlockAt_injective
  apply (MulAction.injective m23M22GeneratorB :
    Function.Injective
      (fun B : Finset (Fin 23) => m23M22GeneratorB • B))
  change m23M22GeneratorB • m23BlockAt i =
    m23M22GeneratorB • m23BlockAt j
  rw [m23M22GeneratorB_blockAt i, m23M22GeneratorB_blockAt j, hij]

private theorem m23M22GeneratorBBlockIndex_surjective :
    Function.Surjective m23M22GeneratorBBlockIndex :=
  Finite.surjective_of_injective m23M22GeneratorBBlockIndex_injective

public theorem m23M22GeneratorB_blocks_smul :
    m23M22GeneratorB • m23Blocks = m23Blocks :=
  m23Blocks_smul_of_reindex
    m23M22GeneratorB m23M22GeneratorBBlockIndex
    m23M22GeneratorBBlockIndex_surjective
    m23M22GeneratorB_blockAt

public theorem m23M22GeneratorB_mem_M23 : m23M22GeneratorB ∈ M23 := by
  rw [mem_M23_iff]
  have h := congrArg
    (fun s : Finset (Finset (Fin 23)) => (s : Set (Finset (Fin 23))))
    m23M22GeneratorB_blocks_smul
  simpa only [Finset.coe_smul_finset] using h

set_option maxHeartbeats 800000


set_option maxHeartbeats 800000

public theorem m22M23PointMap_rightInverse_low
    (i : Fin 12) (hi : m23M22LowIndex i ≠ (9 : Fin 23)) :
    m22M23PointMap
        (m22M23PointMapLeftInverse (m23M22LowIndex i)) =
      m23M22LowIndex i := by
  fin_cases i <;>
    simp [m23M22LowIndex, m22M23PointMap,
      m22M23PointMapLeftInverse] at hi ⊢

set_option maxHeartbeats 800000

public theorem m22M23PointMap_rightInverse_high (i : Fin 11) :
    m22M23PointMap
        (m22M23PointMapLeftInverse (m23M22HighIndex i)) =
      m23M22HighIndex i := by
  fin_cases i <;>
    simp [m23M22HighIndex, m22M23PointMap,
      m22M23PointMapLeftInverse]

set_option maxHeartbeats 800000

public theorem m22M23PointMap_rightInverse_of_ne_nine
    (i : Fin 23) (hi : i ≠ (9 : Fin 23)) :
    m22M23PointMap (m22M23PointMapLeftInverse i) = i := by
  by_cases hlow : i.val < 12
  · let j : Fin 12 := ⟨i.val, hlow⟩
    have hj : m23M22LowIndex j = i := Fin.ext rfl
    simpa [hj] using m22M23PointMap_rightInverse_low j hi
  · have hi12 : 12 ≤ i.val := Nat.le_of_not_gt hlow
    let j : Fin 11 := ⟨i.val - 12, by omega⟩
    have hj : m23M22HighIndex j = i := by
      apply Fin.ext
      simp [m23M22HighIndex, j]
      omega
    simpa [hj] using m22M23PointMap_rightInverse_high j

public theorem m22M23RelabelHom_apply_of_ne_nine
    (g : Equiv.Perm (Fin 22)) (i : Fin 23) (hi : i ≠ (9 : Fin 23)) :
    m22M23RelabelHom g i =
      m22M23PointMap (g (m22M23PointMapLeftInverse i)) := by
  have hright := m22M23PointMap_rightInverse_of_ne_nine i hi
  calc
    m22M23RelabelHom g i =
        m22M23RelabelHom g
          (m22M23PointMap (m22M23PointMapLeftInverse i)) :=
      congrArg (fun x => m22M23RelabelHom g x) hright.symm
    _ = m22M23PointMap (g (m22M23PointMapLeftInverse i)) := by
      change
        (Equiv.Perm.viaEmbeddingHom m22M23PointEmbedding g)
            (m22M23PointEmbedding (m22M23PointMapLeftInverse i)) =
          m22M23PointEmbedding
            (g (m22M23PointMapLeftInverse i))
      rw [Equiv.Perm.viaEmbeddingHom_apply,
        Equiv.Perm.viaEmbedding_apply]

public theorem m22M23RelabelHom_apply_nine
    (g : Equiv.Perm (Fin 22)) :
    m22M23RelabelHom g (9 : Fin 23) = 9 := by
  change (Equiv.Perm.viaEmbeddingHom m22M23PointEmbedding g) (9 : Fin 23) = 9
  rw [Equiv.Perm.viaEmbeddingHom_apply,
    Equiv.Perm.viaEmbedding_apply_of_notMem]
  intro h
  rcases h with ⟨x, hx⟩
  exact m22M23PointMap_ne_nine x hx

set_option maxRecDepth 100000
set_option maxHeartbeats 800000


public theorem m22M23RelabelHom_swap (a b : Fin 22) :
    m22M23RelabelHom (Equiv.swap a b) =
      Equiv.swap (m22M23PointMap a) (m22M23PointMap b) := by
  apply Equiv.ext
  intro i
  by_cases hi : i = (9 : Fin 23)
  · subst i
    rw [m22M23RelabelHom_apply_nine, Equiv.swap_apply_def]
    simp [Ne.symm (m22M23PointMap_ne_nine a),
      Ne.symm (m22M23PointMap_ne_nine b)]
  · rw [m22M23RelabelHom_apply_of_ne_nine _ _ hi]
    have hright := m22M23PointMap_rightInverse_of_ne_nine i hi
    by_cases ha : m22M23PointMapLeftInverse i = a
    · have hiA : i = m22M23PointMap a := by
        rw [← hright, ha]
      subst i
      rw [ha]
      simp
    · by_cases hb : m22M23PointMapLeftInverse i = b
      · have hiB : i = m22M23PointMap b := by
          rw [← hright, hb]
        subst i
        rw [hb]
        simp
      · have hiA : i ≠ m22M23PointMap a := by
          intro h
          apply ha
          rw [← m22M23PointMap_leftInverse a]
          exact congrArg m22M23PointMapLeftInverse h
        have hiB : i ≠ m22M23PointMap b := by
          intro h
          apply hb
          rw [← m22M23PointMap_leftInverse b]
          exact congrArg m22M23PointMapLeftInverse h
        simp [Equiv.swap_apply_def, ha, hb, hiA, hiB, hright]

public theorem m22M23RelabelHom_generatorA_low (i : Fin 12) :
    m22M23RelabelHom m22GeneratorA (m23M22LowIndex i) =
      m23M22GeneratorA (m23M22LowIndex i) := by
  fin_cases i <;>
    simp [m23M22LowIndex, m22GeneratorA, m22M23RelabelHom_swap,
      m22M23PointMap, m23M22GeneratorA, m23M22GeneratorATable,
      Equiv.swap_apply_def]

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public theorem m22M23RelabelHom_generatorA_high (i : Fin 11) :
    m22M23RelabelHom m22GeneratorA (m23M22HighIndex i) =
      m23M22GeneratorA (m23M22HighIndex i) := by
  fin_cases i <;>
    simp [m23M22HighIndex, m22GeneratorA, m22M23RelabelHom_swap,
      m22M23PointMap, m23M22GeneratorA, m23M22GeneratorATable,
      Equiv.swap_apply_def]

public theorem m22M23RelabelHom_generatorA :
    m22M23RelabelHom m22GeneratorA = m23M22GeneratorA := by
  apply Equiv.ext
  intro i
  by_cases hi : i.val < 12
  · let j : Fin 12 := ⟨i.val, hi⟩
    have hj : m23M22LowIndex j = i := Fin.ext rfl
    simpa [hj] using m22M23RelabelHom_generatorA_low j
  · have hi12 : 12 ≤ i.val := Nat.le_of_not_gt hi
    let j : Fin 11 := ⟨i.val - 12, by omega⟩
    have hj : m23M22HighIndex j = i := by
      apply Fin.ext
      simp [m23M22HighIndex, j]
      omega
    simpa [hj] using m22M23RelabelHom_generatorA_high j

set_option maxRecDepth 100000
set_option maxHeartbeats 800000


public theorem m22M23RelabelHom_generatorB_low (i : Fin 12) :
    m22M23RelabelHom m22GeneratorB (m23M22LowIndex i) =
      m23M22GeneratorB (m23M22LowIndex i) := by
  fin_cases i <;>
    simp [m23M22LowIndex, m22GeneratorB, m22M23RelabelHom_swap,
      m22M23PointMap, m23M22GeneratorB, m23M22GeneratorBTable,
      Equiv.swap_apply_def]

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

public theorem m22M23RelabelHom_generatorB_high (i : Fin 11) :
    m22M23RelabelHom m22GeneratorB (m23M22HighIndex i) =
      m23M22GeneratorB (m23M22HighIndex i) := by
  fin_cases i <;>
    simp [m23M22HighIndex, m22GeneratorB, m22M23RelabelHom_swap,
      m22M23PointMap, m23M22GeneratorB, m23M22GeneratorBTable,
      Equiv.swap_apply_def]

public theorem m22M23RelabelHom_generatorB :
    m22M23RelabelHom m22GeneratorB = m23M22GeneratorB := by
  apply Equiv.ext
  intro i
  by_cases hi : i.val < 12
  · let j : Fin 12 := ⟨i.val, hi⟩
    have hj : m23M22LowIndex j = i := Fin.ext rfl
    simpa [hj] using m22M23RelabelHom_generatorB_low j
  · have hi12 : 12 ≤ i.val := Nat.le_of_not_gt hi
    let j : Fin 11 := ⟨i.val - 12, by omega⟩
    have hj : m23M22HighIndex j = i := by
      apply Fin.ext
      simp [m23M22HighIndex, j]
      omega
    simpa [hj] using m22M23RelabelHom_generatorB_high j

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- Relabelling every element of the Atlas-generated M22 subgroup preserves W23. -/
public theorem m22AtlasM23RelabelHom_mem_M23 (g : m22Atlas) :
    m22M23RelabelHom (g : Equiv.Perm (Fin 22)) ∈ M23 := by
  have hle : m22Atlas ≤ M23.comap m22M23RelabelHom := by
    rw [m22Atlas_eq_closure, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · change m22M23RelabelHom m22GeneratorA ∈ M23
      rw [m22M23RelabelHom_generatorA]
      exact m23M22GeneratorA_mem_M23
    · change m22M23RelabelHom m22GeneratorB ∈ M23
      rw [m22M23RelabelHom_generatorB]
      exact m23M22GeneratorB_mem_M23
  exact hle g.property

/-- Relabel the Atlas-generated M22 subgroup inside M23. -/
@[expose] public noncomputable def m22AtlasToM23Hom : m22Atlas →* M23 :=
  (m22M23RelabelHom.comp m22Atlas.subtype).codRestrict M23
    (fun g => m22AtlasM23RelabelHom_mem_M23 g)

public theorem m22AtlasToM23Hom_apply_nine (g : m22Atlas) :
    ((m22AtlasToM23Hom g : M23) : Equiv.Perm (Fin 23)) (9 : Fin 23) = 9 := by
  change m22M23RelabelHom (g : Equiv.Perm (Fin 22)) (9 : Fin 23) = 9
  exact m22M23RelabelHom_apply_nine _

/-- The relabelled Atlas M22 homomorphism valued in the point-9 stabilizer of M23. -/
@[expose] public noncomputable def m22AtlasToM23PointStabilizerHom :
    m22Atlas →* MulAction.stabilizer M23 (9 : Fin 23) :=
  m22AtlasToM23Hom.codRestrict (MulAction.stabilizer M23 (9 : Fin 23))
    (fun g => by
      rw [MulAction.mem_stabilizer_iff]
      exact m22AtlasToM23Hom_apply_nine g)

public theorem m22AtlasToM23PointStabilizerHom_injective :
    Function.Injective m22AtlasToM23PointStabilizerHom := by
  intro g h hgh
  apply Subtype.ext
  apply Equiv.Perm.viaEmbeddingHom_injective m22M23PointEmbedding
  have hPerm := congrArg
    (fun k : MulAction.stabilizer M23 (9 : Fin 23) =>
      ((k : M23) : Equiv.Perm (Fin 23))) hgh
  change m22M23RelabelHom (g : Equiv.Perm (Fin 22)) =
    m22M23RelabelHom (h : Equiv.Perm (Fin 22)) at hPerm
  exact hPerm

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise

@[expose] public def m23Standard23CycleList : List (Fin 23) :=
  [1, 23, 14, 11, 7, 13, 5, 22, 20, 6, 10, 3,
    8, 15, 12, 21, 19, 2, 4, 9, 18, 17, 16]

@[expose] public def m23Standard23CycleTable : Fin 23 → Fin 23 :=
  ![14, 23, 4, 8, 9, 22, 10, 13, 15, 18, 3, 7,
    21, 5, 11, 12, 1, 16, 17, 2, 6, 19, 20]

@[expose] public def m23Standard23CycleInvTable : Fin 23 → Fin 23 :=
  ![1, 16, 19, 10, 2, 13, 20, 11, 3, 4, 6, 14,
    15, 7, 23, 8, 17, 18, 9, 21, 22, 12, 5]

/-- The explicit Atlas-label 23-cycle, represented by direct lookup tables. -/
@[expose] public def m23Standard23Cycle : Equiv.Perm (Fin 23) where
  toFun := m23Standard23CycleTable
  invFun := m23Standard23CycleInvTable
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

public theorem m23Standard23Cycle_apply (i : Fin 23) :
    m23Standard23Cycle i = m23Standard23CycleTable i := rfl

/-- The table permutation agrees with the cyclic-list presentation. -/
public theorem m23Standard23Cycle_eq_formPerm :
    m23Standard23Cycle = List.formPerm m23Standard23CycleList := by
  apply Equiv.ext
  intro i
  have hNodup : m23Standard23CycleList.Nodup := by decide +kernel
  fin_cases i
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 1 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 0 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 17 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 11 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 18 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 6 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 9 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 4 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 12 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 19 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 10 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 3 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 14 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 5 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 2 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 13 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 22 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 21 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 20 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 16 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 8 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 15 (by decide +kernel)).symm
  · exact (List.formPerm_apply_getElem m23Standard23CycleList hNodup 7 (by decide +kernel)).symm

/-- The block-index permutation induced by the displayed 23-cycle. -/
@[expose] public def m23Standard23BlockIndexArray : Array (Fin 253) := #[
  188, 100, 183, 176, 22, 133, 197, 8, 198, 199, 144, 96, 42, 44, 200, 40, 78, 182, 143, 175, 98, 68, 225, 213,
  88, 226, 148, 70, 126, 160, 214, 125, 234, 155, 9, 233, 69, 247, 118, 170, 55, 248, 122, 211, 169, 32, 223, 111,
  62, 212, 4, 66, 251, 123, 207, 250, 154, 172, 224, 112, 56, 119, 63, 171, 249, 30, 206, 19, 84, 67, 252, 124,
  205, 20, 147, 28, 86, 193, 95, 41, 141, 39, 195, 77, 194, 142, 181, 43, 196, 134, 99, 174, 7, 101, 23, 177,
  185, 189, 45, 184, 139, 79, 38, 97, 178, 187, 140, 173, 102, 192, 48, 6, 136, 179, 5, 24, 94, 186, 180, 80,
  104, 135, 137, 191, 47, 37, 103, 190, 93, 46, 21, 0, 138, 165, 242, 203, 17, 208, 115, 241, 153, 120, 27, 64,
  243, 121, 245, 60, 210, 221, 110, 31, 168, 204, 244, 18, 65, 246, 83, 29, 167, 3, 209, 54, 116, 166, 222, 109,
  61, 53, 117, 87, 146, 215, 57, 235, 129, 237, 73, 82, 156, 89, 228, 216, 10, 227, 161, 33, 72, 150, 15, 49,
  128, 157, 236, 105, 71, 201, 127, 149, 1, 74, 158, 132, 152, 240, 106, 76, 163, 11, 229, 219, 91, 232, 35, 25,
  90, 51, 114, 218, 14, 239, 75, 131, 26, 238, 159, 85, 151, 202, 16, 50, 130, 113, 217, 107, 59, 231, 162, 81,
  34, 52, 220, 13, 145, 2, 92, 164, 36, 108, 58, 12, 230]

public theorem m23Standard23BlockIndexArray_size :
    m23Standard23BlockIndexArray.size = 253 := by decide +kernel

public def m23Standard23BlockIndex (i : Fin 253) : Fin 253 :=
  m23Standard23BlockIndexArray[i.val]'(by
    rw [m23Standard23BlockIndexArray_size]
    exact i.isLt)

private theorem m23Standard23Cycle_block_bits (i : Fin 253) (x : Fin 23) :
    (m23BlockMask i).testBit (m23Standard23Cycle.symm x).val =
      (m23BlockMask (m23Standard23BlockIndex i)).testBit x.val := by
  revert i x
  decide +kernel

/-- Kernel-checked certificate for all 253 block images. -/
public theorem m23Standard23Cycle_blockAt_smul (i : Fin 253) :
    m23Standard23Cycle • m23BlockAt i =
      m23BlockAt (m23Standard23BlockIndex i) :=
  m23Perm_smul_blockAt_of_bits _ _ _ (m23Standard23Cycle_block_bits i)

private theorem m23Standard23BlockIndex_injective :
    Function.Injective m23Standard23BlockIndex := by
  intro i j hij
  apply m23BlockAt_injective
  apply (MulAction.injective m23Standard23Cycle :
    Function.Injective
      (fun B : Finset (Fin 23) => m23Standard23Cycle • B))
  change m23Standard23Cycle • m23BlockAt i =
    m23Standard23Cycle • m23BlockAt j
  rw [m23Standard23Cycle_blockAt_smul i,
    m23Standard23Cycle_blockAt_smul j, hij]

private theorem m23Standard23BlockIndex_surjective :
    Function.Surjective m23Standard23BlockIndex :=
  Finite.surjective_of_injective m23Standard23BlockIndex_injective

public theorem m23Standard23BlockIndex_image :
    Finset.univ.image m23Standard23BlockIndex = Finset.univ := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact m23Standard23BlockIndex_surjective j

public theorem m23Standard23Cycle_smul_blocks :
    m23Standard23Cycle • m23Blocks = m23Blocks :=
  m23Blocks_smul_of_reindex
    m23Standard23Cycle m23Standard23BlockIndex
    m23Standard23BlockIndex_surjective
    m23Standard23Cycle_blockAt_smul

public theorem m23Standard23Cycle_mem_M23 : m23Standard23Cycle ∈ M23 := by
  rw [mem_M23_iff]
  have hSet := congrArg
    (fun s : Finset (Finset (Fin 23)) => (s : Set (Finset (Fin 23))))
    m23Standard23Cycle_smul_blocks
  simpa only [Finset.coe_smul_finset] using hSet

/-- The standard 23-cycle, certified directly as an automorphism of W23. -/
@[expose] public noncomputable def m23Standard23 : M23 :=
  ⟨m23Standard23Cycle, m23Standard23Cycle_mem_M23⟩

/-- The M23 element acts as the displayed 23-cycle. -/
public theorem m23Standard23_coe :
    (m23Standard23 : Equiv.Perm (Fin 23)) = m23Standard23Cycle := rfl

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


/-- The displayed permutation underlying `m23Standard23` is a single cycle. -/
public theorem m23Standard23Cycle_isCycle :
    m23Standard23Cycle.IsCycle := by
  rw [m23Standard23Cycle_eq_formPerm]
  apply List.isCycle_formPerm
  · decide +kernel
  · norm_num [m23Standard23CycleList]

/-- The standard 23-cycle moves every point of the natural M23 action. -/
public theorem m23Standard23_ne_fixed (i : Fin 23) :
    (m23Standard23 : Equiv.Perm (Fin 23)) i ≠ i := by
  rw [m23Standard23_coe, m23Standard23Cycle_apply]
  fin_cases i <;>
    intro h <;>
    have hval := congrArg Fin.val h <;>
    norm_num [m23Standard23CycleTable, Matrix.cons_val] at hval

/-- The natural degree-23 action of M23 is transitive. -/
public theorem m23_isPretransitive : MulAction.IsPretransitive M23 (Fin 23) := by
  constructor
  intro x y
  obtain ⟨n, hn⟩ := m23Standard23Cycle_isCycle.exists_pow_eq
    (by simpa [m23Standard23_coe] using m23Standard23_ne_fixed x)
    (by simpa [m23Standard23_coe] using m23Standard23_ne_fixed y)
  refine ⟨m23Standard23 ^ n, ?_⟩
  change ((m23Standard23 : Equiv.Perm (Fin 23)) ^ n) x = y
  simpa [m23Standard23_coe] using hn

public noncomputable instance : MulAction.IsPretransitive M23 (Fin 23) :=
  m23_isPretransitive

/-- A transitive action of prime degree 23 is primitive. -/
public theorem m23_isPreprimitive : MulAction.IsPreprimitive M23 (Fin 23) := by
  apply MulAction.IsPreprimitive.of_prime_card
  simpa using (by decide +kernel : Nat.Prime 23)

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise

/-- Relabel the 22 points as the complement of Atlas point 9. -/
@[expose] public noncomputable def m22M23PointComplementEquiv :
    Fin 22 ≃ {x : Fin 23 // x ≠ (9 : Fin 23)} where
  toFun i := ⟨m22M23PointMap i, m22M23PointMap_ne_nine i⟩
  invFun x := m22M23PointMapLeftInverse x.1
  left_inv := m22M23PointMap_leftInverse
  right_inv := by
    intro x
    apply Subtype.ext
    exact m22M23PointMap_rightInverse_of_ne_nine x.1 x.2

public theorem m23PointStabilizerNine_ne_nine_iff
    (g : MulAction.stabilizer M23 (9 : Fin 23)) (x : Fin 23) :
    ((g : M23) : Equiv.Perm (Fin 23)) x ≠ (9 : Fin 23) ↔
      x ≠ (9 : Fin 23) := by
  have hFix : ((g : M23) : Equiv.Perm (Fin 23)) (9 : Fin 23) =
      (9 : Fin 23) := g.property
  simpa only [hFix] using
    not_congr
      (((g : M23) : Equiv.Perm (Fin 23)).injective.eq_iff :
        ((g : M23) : Equiv.Perm (Fin 23)) x =
            ((g : M23) : Equiv.Perm (Fin 23)) (9 : Fin 23) ↔
          x = (9 : Fin 23))

@[expose] public noncomputable def m23PointStabilizerNineComplementHom :
    MulAction.stabilizer M23 (9 : Fin 23) →*
      Equiv.Perm {x : Fin 23 // x ≠ (9 : Fin 23)} where
  toFun g :=
    ((g : M23) : Equiv.Perm (Fin 23)).subtypePerm
      (m23PointStabilizerNine_ne_nine_iff g)
  map_one' := by
    ext x
    rfl
  map_mul' g h := by
    ext x
    rfl

/-- Restrict a point-9 stabilizer element to the relabelled 22-point complement. -/
@[expose] public noncomputable def m23PointStabilizerNineRestrictHom :
    MulAction.stabilizer M23 (9 : Fin 23) →* Equiv.Perm (Fin 22) :=
  m22M23PointComplementEquiv.symm.permCongrHom.toMonoidHom.comp
    m23PointStabilizerNineComplementHom

public theorem m23PointStabilizerNineRestrictHom_apply
    (g : MulAction.stabilizer M23 (9 : Fin 23)) (i : Fin 22) :
    m22M23PointMap (m23PointStabilizerNineRestrictHom g i) =
      ((g : M23) : Equiv.Perm (Fin 23)) (m22M23PointMap i) := by
  change
    (m22M23PointComplementEquiv
      (m22M23PointComplementEquiv.symm.permCongr
        (m23PointStabilizerNineComplementHom g) i)).1 =
      ((g : M23) : Equiv.Perm (Fin 23))
        (m22M23PointComplementEquiv i).1
  rw [Equiv.permCongr_apply, m22M23PointComplementEquiv.apply_symm_apply]
  rfl

/-- Extending the restricted permutation recovers the original point stabilizer element. -/
public theorem m22M23RelabelHom_restrict
    (g : MulAction.stabilizer M23 (9 : Fin 23)) :
    m22M23RelabelHom (m23PointStabilizerNineRestrictHom g) =
      ((g : M23) : Equiv.Perm (Fin 23)) := by
  apply Equiv.ext
  intro x
  by_cases hx : x = (9 : Fin 23)
  · subst x
    rw [m22M23RelabelHom_apply_nine]
    exact g.property.symm
  · rw [m22M23RelabelHom_apply_of_ne_nine _ x hx,
      m23PointStabilizerNineRestrictHom_apply,
      m22M23PointMap_rightInverse_of_ne_nine x hx]

@[expose] public def m22M23LiftBlock (B : Finset (Fin 22)) : Finset (Fin 23) :=
  B.map m22M23PointEmbedding

@[expose] public def m22M23AugmentedBlock (B : Finset (Fin 22)) : Finset (Fin 23) :=
  insert (9 : Fin 23) (m22M23LiftBlock B)

public theorem m22M23LiftBlock_not_mem_nine (B : Finset (Fin 22)) :
    (9 : Fin 23) ∉ m22M23LiftBlock B := by
  intro h
  rcases Finset.mem_map.mp h with ⟨i, -, hi⟩
  exact m22M23PointMap_ne_nine i hi

public theorem m22M23AugmentedBlock_injective :
    Function.Injective m22M23AugmentedBlock := by
  intro B C hBC
  have hErase := congrArg
    (fun S : Finset (Fin 23) => S.erase (9 : Fin 23)) hBC
  rw [m22M23AugmentedBlock,
    Finset.erase_insert (m22M23LiftBlock_not_mem_nine B)] at hErase
  rw [m22M23AugmentedBlock,
    Finset.erase_insert (m22M23LiftBlock_not_mem_nine C)] at hErase
  exact Finset.map_injective m22M23PointEmbedding (by
    simpa [m22M23LiftBlock] using hErase)

private def m22M23AugmentedBlockIndexArray : Array (Fin 253) := #[
  32, 120, 237, 201, 189, 79, 150, 165, 157, 127, 118, 10, 41,
  248, 73, 177, 241, 213, 198, 72, 227, 82, 139, 153, 161, 15,
  122, 97, 208, 223, 188, 235, 57, 64, 236, 211, 38, 88, 1,
  89, 156, 33, 170, 23, 27, 141, 169, 149, 133, 101, 105, 17,
  129, 115, 95, 111, 8, 128, 242, 55, 243, 178, 228, 197, 71,
  203, 215, 185, 247, 225, 68, 193, 45, 62, 184, 216, 49]

theorem m22M23AugmentedBlockIndexArray_size :
    m22M23AugmentedBlockIndexArray.size = 77 := by decide +kernel

def m22M23AugmentedBlockIndex (i : Fin 77) : Fin 253 :=
  m22M23AugmentedBlockIndexArray[i.val]'(by
    rw [m22M23AugmentedBlockIndexArray_size]
    exact i.isLt)

theorem m22M23AugmentedBlockAt (i : Fin 77) :
    m22M23AugmentedBlock (m22BlockAt i) =
      m23BlockAt (m22M23AugmentedBlockIndex i) := by
  revert i
  decide +kernel

theorem m22M23AugmentedBlockIndex_image :
    Finset.univ.image m22M23AugmentedBlockIndex =
      Finset.univ.filter (fun j => (9 : Fin 23) ∈ m23BlockAt j) := by
  decide +kernel

/-- The 77 M22 hexads are exactly the W23 heptads through point 9. -/
public theorem m23Blocks_through_nine :
    m23Blocks.filter (fun B => (9 : Fin 23) ∈ B) =
      m22Blocks.image m22M23AugmentedBlock := by
  ext B
  constructor
  · intro hB
    rcases Finset.mem_filter.mp hB with ⟨hBlocks, hNine⟩
    rw [m23Blocks] at hBlocks
    rcases Finset.mem_image.mp hBlocks with ⟨j, -, rfl⟩
    have hj :
        j ∈ Finset.univ.filter
          (fun k => (9 : Fin 23) ∈ m23BlockAt k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNine⟩
    rw [← m22M23AugmentedBlockIndex_image] at hj
    rcases Finset.mem_image.mp hj with ⟨i, -, hij⟩
    apply Finset.mem_image.mpr
    refine ⟨m22BlockAt i, ?_, ?_⟩
    · rw [← m22BlockAt_image]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · rw [m22M23AugmentedBlockAt i, hij]
  · intro hB
    rcases Finset.mem_image.mp hB with ⟨C, hC, rfl⟩
    rw [← m22BlockAt_image] at hC
    rcases Finset.mem_image.mp hC with ⟨i, -, rfl⟩
    rw [m22M23AugmentedBlockAt i]
    apply Finset.mem_filter.mpr
    constructor
    · rw [m23Blocks]
      exact Finset.mem_image.mpr
        ⟨m22M23AugmentedBlockIndex i, Finset.mem_univ _, rfl⟩
    · have hi :
          m22M23AugmentedBlockIndex i ∈
            Finset.univ.image m22M23AugmentedBlockIndex :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      rw [m22M23AugmentedBlockIndex_image] at hi
      exact (Finset.mem_filter.mp hi).2

public theorem m23PointStabilizerNine_smul_m23Blocks
    (g : MulAction.stabilizer M23 (9 : Fin 23)) :
    ((g : M23) : Equiv.Perm (Fin 23)) • m23Blocks = m23Blocks := by
  have hg := (mem_M23_iff ((g : M23) : Equiv.Perm (Fin 23))).mp
    (g : M23).property
  apply Finset.coe_injective
  simpa only [Finset.coe_smul_finset] using hg

public theorem m23PointStabilizerNine_smul_liftBlock
    (g : MulAction.stabilizer M23 (9 : Fin 23)) (B : Finset (Fin 22)) :
    ((g : M23) : Equiv.Perm (Fin 23)) • m22M23LiftBlock B =
      m22M23LiftBlock (m23PointStabilizerNineRestrictHom g • B) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_smul_finset.mp hx with ⟨y, hy, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨a, ha, rfl⟩
    rw [m22M23LiftBlock, Finset.mem_map]
    exact ⟨m23PointStabilizerNineRestrictHom g a,
      Finset.smul_mem_smul_finset ha,
      m23PointStabilizerNineRestrictHom_apply g a⟩
  · intro hx
    rw [m22M23LiftBlock] at hx
    rcases Finset.mem_map.mp hx with ⟨a, ha, hax⟩
    rcases Finset.mem_smul_finset.mp ha with ⟨b, hb, rfl⟩
    apply Finset.mem_smul_finset.mpr
    refine ⟨m22M23PointMap b, Finset.mem_map.mpr ⟨b, hb, rfl⟩, ?_⟩
    change ((g : M23) : Equiv.Perm (Fin 23)) (m22M23PointMap b) = x
    rw [← m23PointStabilizerNineRestrictHom_apply g b]
    exact hax

public theorem m23PointStabilizerNine_smul_augmentedBlock
    (g : MulAction.stabilizer M23 (9 : Fin 23)) (B : Finset (Fin 22)) :
    ((g : M23) : Equiv.Perm (Fin 23)) • m22M23AugmentedBlock B =
      m22M23AugmentedBlock (m23PointStabilizerNineRestrictHom g • B) := by
  rw [m22M23AugmentedBlock, m22M23AugmentedBlock,
    Finset.smul_finset_insert]
  change
    insert (((g : M23) : Equiv.Perm (Fin 23)) (9 : Fin 23))
        (((g : M23) : Equiv.Perm (Fin 23)) • m22M23LiftBlock B) =
      insert (9 : Fin 23)
        (m22M23LiftBlock (m23PointStabilizerNineRestrictHom g • B))
  rw [show ((g : M23) : Equiv.Perm (Fin 23)) (9 : Fin 23) =
    (9 : Fin 23) from g.property,
    m23PointStabilizerNine_smul_liftBlock]

public theorem m23PointStabilizerNine_smul_m22Blocks
    (g : MulAction.stabilizer M23 (9 : Fin 23)) :
    m23PointStabilizerNineRestrictHom g • m22Blocks = m22Blocks := by
  apply Finset.eq_of_subset_of_card_le
  · intro C hC
    rcases Finset.mem_smul_finset.mp hC with ⟨B, hB, rfl⟩
    have hAugmented : m22M23AugmentedBlock B ∈ m23Blocks := by
      have hImage : m22M23AugmentedBlock B ∈
          m22Blocks.image m22M23AugmentedBlock :=
        Finset.mem_image.mpr ⟨B, hB, rfl⟩
      rw [← m23Blocks_through_nine] at hImage
      exact (Finset.mem_filter.mp hImage).1
    have hMoved :
        ((g : M23) : Equiv.Perm (Fin 23)) • m22M23AugmentedBlock B ∈
          m23Blocks := by
      rw [← m23PointStabilizerNine_smul_m23Blocks g]
      exact Finset.smul_mem_smul_finset hAugmented
    have hMovedNine : (9 : Fin 23) ∈
        ((g : M23) : Equiv.Perm (Fin 23)) • m22M23AugmentedBlock B := by
      rw [m23PointStabilizerNine_smul_augmentedBlock]
      exact Finset.mem_insert_self _ _
    have hFiltered :
        ((g : M23) : Equiv.Perm (Fin 23)) • m22M23AugmentedBlock B ∈
          m23Blocks.filter (fun D => (9 : Fin 23) ∈ D) :=
      Finset.mem_filter.mpr ⟨hMoved, hMovedNine⟩
    rw [m23Blocks_through_nine] at hFiltered
    rcases Finset.mem_image.mp hFiltered with ⟨B', hB', hB'Eq⟩
    have hEq : B' = m23PointStabilizerNineRestrictHom g • B := by
      apply m22M23AugmentedBlock_injective
      rw [hB'Eq, m23PointStabilizerNine_smul_augmentedBlock]
    rwa [← hEq]
  · simp

public theorem m23PointStabilizerNineRestrictHom_mem_m22DesignAut
    (g : MulAction.stabilizer M23 (9 : Fin 23)) :
    m23PointStabilizerNineRestrictHom g ∈ m22DesignAut := by
  rw [m22DesignAut, SteinerSystem.mem_aut_iff]
  have hSet := congrArg
    (fun s : Finset (Finset (Fin 22)) => (s : Set (Finset (Fin 22))))
    (m23PointStabilizerNine_smul_m22Blocks g)
  simpa only [m22WittDesign, SteinerSystem.ofPairwiseIntersection_blocks,
    Finset.coe_smul_finset] using hSet

/-- Restriction from the M23 point stabilizer to the full M22-design automorphism group. -/
@[expose] public noncomputable def m23PointStabilizerNineToM22DesignAut :
    MulAction.stabilizer M23 (9 : Fin 23) →* m22DesignAut :=
  m23PointStabilizerNineRestrictHom.codRestrict m22DesignAut
    m23PointStabilizerNineRestrictHom_mem_m22DesignAut

public theorem m23PointStabilizerNineToM22DesignAut_injective :
    Function.Injective m23PointStabilizerNineToM22DesignAut := by
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  have hRestrict :
      m23PointStabilizerNineRestrictHom g =
        m23PointStabilizerNineRestrictHom h :=
    congrArg (fun k : m22DesignAut => (k : Equiv.Perm (Fin 22))) hgh
  have hExtend := congrArg m22M23RelabelHom hRestrict
  simpa only [m22M23RelabelHom_restrict] using hExtend

def m22OddPairSwapBlockIndexArray : Array (Fin 77) := #[
  0, 1, 2, 4, 3, 5, 8, 7, 6, 11, 10, 9, 16, 18, 15, 14, 12,
  17, 13, 20, 19, 21, 24, 23, 22, 27, 26, 25, 33, 35, 30, 32,
  31, 28, 36, 29, 34, 37, 39, 38, 43, 47, 42, 40, 45, 44, 48,
  41, 46, 52, 57, 51, 49, 54, 53, 56, 55, 50, 65, 68, 71, 61,
  62, 73, 64, 58, 67, 66, 59, 70, 69, 60, 72, 63, 74, 75, 76]

theorem m22OddPairSwapBlockIndexArray_size :
    m22OddPairSwapBlockIndexArray.size = 77 := by decide +kernel

def m22OddPairSwapBlockIndex (i : Fin 77) : Fin 77 :=
  m22OddPairSwapBlockIndexArray[i.val]'(by
    rw [m22OddPairSwapBlockIndexArray_size]
    exact i.isLt)

theorem m22OddPairSwapBlockIndex_image :
    Finset.univ.image m22OddPairSwapBlockIndex = Finset.univ := by
  decide +kernel

theorem m22OddPairSwap_blockAt (i : Fin 77) :
    m22OddPairSwap • m22BlockAt i =
      m22BlockAt (m22OddPairSwapBlockIndex i) := by
  revert i
  decide +kernel

/-- The simultaneous seven-pair swap in the derived 22-point design is a design automorphism. -/
public theorem m22OddPairSwap_mem_m22DesignAut :
    m22OddPairSwap ∈ m22DesignAut := by
  rw [m22DesignAut, SteinerSystem.mem_aut_iff]
  have hFinset : m22OddPairSwap • m22Blocks = m22Blocks :=
    m22_blocks_smul_of_index
      m22OddPairSwap m22OddPairSwapBlockIndex
      m22OddPairSwapBlockIndex_image m22OddPairSwap_blockAt
  have hSet := congrArg
    (fun s : Finset (Finset (Fin 22)) => (s : Set (Finset (Fin 22)))) hFinset
  simpa only [m22WittDesign, SteinerSystem.ofPairwiseIntersection_blocks,
    Finset.coe_smul_finset] using hSet

/-- The relabelled seven-pair swap on the complement of point 9. -/
@[expose] public def m23M22OddPairSwap : Equiv.Perm (Fin 23) :=
  Equiv.swap 5 21 * Equiv.swap 17 12 * Equiv.swap 16 4 *
    Equiv.swap 14 10 * Equiv.swap 13 6 * Equiv.swap 15 19 *
    Equiv.swap 11 1

public theorem m22M23RelabelHom_oddPairSwap :
    m22M23RelabelHom m22OddPairSwap = m23M22OddPairSwap := by
  simp [m22OddPairSwap, m23M22OddPairSwap, map_mul,
    m22M23RelabelHom_swap, m22M23PointMap, Matrix.cons_val]

public theorem m23M22OddPairSwap_not_mem_M23 : m23M22OddPairSwap ∉ M23 := by
  intro h
  have hSet := (mem_M23_iff m23M22OddPairSwap).mp h
  have hFinset : m23M22OddPairSwap • m23Blocks = m23Blocks := by
    apply Finset.coe_injective
    simpa only [Finset.coe_smul_finset] using hSet
  have hBlock : m23BlockAt (0 : Fin 253) ∈ m23Blocks := by
    rw [m23Blocks]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hMoved : m23M22OddPairSwap • m23BlockAt (0 : Fin 253) ∈ m23Blocks := by
    rw [← hFinset]
    exact Finset.smul_mem_smul_finset hBlock
  have hCalc :
      m23M22OddPairSwap • m23BlockAt (0 : Fin 253) =
        ({1, 2, 3, 11, 12, 16, 21} : Finset (Fin 23)) := by
    decide +kernel
  rw [hCalc] at hMoved
  rw [m23Blocks] at hMoved
  rcases Finset.mem_image.mp hMoved with ⟨j, -, hj⟩
  have hj0 : j ≠ (0 : Fin 253) := by
    intro h
    subst j
    have hne :
        m23BlockAt (0 : Fin 253) ≠
          ({1, 2, 3, 11, 12, 16, 21} : Finset (Fin 23)) := by
      decide +kernel
    exact hne hj
  have hlt := m23BlockAt_inter j 0 hj0
  have hcard :
      (m23BlockAt j ∩ m23BlockAt (0 : Fin 253)).card = 4 := by
    rw [hj]
    decide +kernel
  omega

public theorem m22M23RelabelHom_oddPairSwap_not_mem_M23 :
    m22M23RelabelHom m22OddPairSwap ∉ M23 := by
  rw [m22M23RelabelHom_oddPairSwap]
  exact m23M22OddPairSwap_not_mem_M23

public theorem m23PointStabilizerNineToM22DesignAut_range_ne_top :
    m23PointStabilizerNineToM22DesignAut.range ≠ ⊤ := by
  intro hTop
  let odd : m22DesignAut :=
    ⟨m22OddPairSwap, m22OddPairSwap_mem_m22DesignAut⟩
  have hOddRange : odd ∈ m23PointStabilizerNineToM22DesignAut.range := by
    rw [hTop]
    exact Subgroup.mem_top odd
  rcases hOddRange with ⟨g, hg⟩
  have hRestrict :
      m23PointStabilizerNineRestrictHom g = m22OddPairSwap :=
    congrArg (fun k : m22DesignAut => (k : Equiv.Perm (Fin 22))) hg
  have hExtend := congrArg m22M23RelabelHom hRestrict
  rw [m22M23RelabelHom_restrict] at hExtend
  apply m22M23RelabelHom_oddPairSwap_not_mem_M23
  rw [← hExtend]
  exact (g : M23).property

/-- The even part of the full 22-point design automorphism group. -/
@[expose] public noncomputable def m22DesignAutEven : Subgroup m22DesignAut :=
  (alternatingGroup (Fin 22)).comap m22DesignAut.subtype

/-- The current M22 definition is exactly the even part of the design automorphism group. -/
@[expose] public def m22EquivM22DesignAutEven : M22 ≃* m22DesignAutEven where
  toFun g := ⟨⟨(g : Equiv.Perm (Fin 22)), g.property.1⟩, g.property.2⟩
  invFun g :=
    ⟨((g : m22DesignAut) : Equiv.Perm (Fin 22)),
      ⟨(g : m22DesignAut).property, g.property⟩⟩
  left_inv _g := Subtype.ext rfl
  right_inv _g := Subtype.ext rfl
  map_mul' _ _ := rfl

public theorem m22DesignAutEven_index_le_two : m22DesignAutEven.index ≤ 2 := by
  have hRel :
      (alternatingGroup (Fin 22)).relIndex m22DesignAut ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right
      (H := alternatingGroup (Fin 22)) (K := m22DesignAut) (L := ⊤)
      le_top (by simp)
    simpa [Subgroup.relIndex_top_right] using h
  simpa [m22DesignAutEven, Subgroup.relIndex] using hRel

public theorem m22DesignAut_card_le : Nat.card m22DesignAut ≤ 887040 := by
  have hCardEven : Nat.card M22 = Nat.card m22DesignAutEven :=
    Nat.card_congr m22EquivM22DesignAutEven.toEquiv
  have hMul := Subgroup.card_mul_index m22DesignAutEven
  calc
    Nat.card m22DesignAut =
        Nat.card m22DesignAutEven * m22DesignAutEven.index := hMul.symm
    _ ≤ 443520 * 2 := Nat.mul_le_mul
      (by rw [← hCardEven, m22_order]) m22DesignAutEven_index_le_two
    _ = 887040 := by norm_num

public theorem m23PointStabilizerNine_card :
    Nat.card (MulAction.stabilizer M23 (9 : Fin 23)) = 443520 := by
  let R := m23PointStabilizerNineToM22DesignAut
  let K := R.range
  have hRInj : Function.Injective R := by
    simpa [R] using m23PointStabilizerNineToM22DesignAut_injective
  have hRangeInj : Function.Injective R.rangeRestrict := by
    intro g h hgh
    apply hRInj
    exact congrArg Subtype.val hgh
  have hCardRange :
      Nat.card (MulAction.stabilizer M23 (9 : Fin 23)) = Nat.card K := by
    exact Nat.card_congr
      (Equiv.ofBijective R.rangeRestrict
        ⟨hRangeInj, R.rangeRestrict_surjective⟩)
  have hLower :
      443520 ≤ Nat.card (MulAction.stabilizer M23 (9 : Fin 23)) := by
    rw [← m22Atlas_order]
    exact Nat.card_le_card_of_injective
      m22AtlasToM23PointStabilizerHom
      m22AtlasToM23PointStabilizerHom_injective
  have hIndex : 2 ≤ K.index := by
    simpa [K, R] using (Nat.succ_le_iff.mpr
      (Subgroup.one_lt_index_of_ne_top
        m23PointStabilizerNineToM22DesignAut_range_ne_top))
  have hMul := Subgroup.card_mul_index K
  have hTwice : 2 * Nat.card K ≤ Nat.card m22DesignAut := by
    rw [Nat.mul_comm]
    calc
      Nat.card K * 2 ≤ Nat.card K * K.index :=
        Nat.mul_le_mul_left (Nat.card K) hIndex
      _ = Nat.card m22DesignAut := hMul
  have hUpper : Nat.card K ≤ 443520 := by
    have h := hTwice.trans m22DesignAut_card_le
    omega
  rw [hCardRange] at hLower
  omega

public theorem m22AtlasToM23PointStabilizerHom_bijective :
    Function.Bijective m22AtlasToM23PointStabilizerHom := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨m22AtlasToM23PointStabilizerHom_injective, ?_⟩
  rw [m22Atlas_order, m23PointStabilizerNine_card]

/-- The Atlas-generated M22 subgroup is the point-9 stabilizer in M23. -/
@[expose] public noncomputable def m22AtlasEquivM23PointStabilizer :
    m22Atlas ≃* MulAction.stabilizer M23 (9 : Fin 23) :=
  MulEquiv.ofBijective m22AtlasToM23PointStabilizerHom
    m22AtlasToM23PointStabilizerHom_bijective

/-- The Steiner-even and Atlas-generated realizations of M22 are canonically identified. -/
@[expose] public noncomputable def m22EquivM22Atlas : M22 ≃* m22Atlas where
  toFun g := ⟨g, by
    rw [m22Atlas_eq_M22]
    exact g.property⟩
  invFun g := ⟨g, by
    rw [← m22Atlas_eq_M22]
    exact g.property⟩
  left_inv g := Subtype.ext rfl
  right_inv g := Subtype.ext rfl
  map_mul' _ _ := rfl

/-- M22 is the point-9 stabilizer in the natural degree-23 action of M23. -/
@[expose] public noncomputable def m23EquivM22PointStabilizer :
    M22 ≃* MulAction.stabilizer M23 (9 : Fin 23) :=
  m22EquivM22Atlas.trans m22AtlasEquivM23PointStabilizer

/-- The explicit extension homomorphism, exposed here for efficient pointwise calculations. -/
@[expose] public noncomputable def m23SimplicityExtendHom :
    M23 →* MulAction.stabilizer M24 (24 : Fin 24) :=
  (m23ExtendHom.codRestrict M24 (fun g => m23Extend_mem_M24 g)).codRestrict
    (MulAction.stabilizer M24 (24 : Fin 24)) (fun g => by
      rw [MulAction.mem_stabilizer_iff]
      exact m23ExtendHom_apply_24 g)

public theorem m23SimplicityExtendHom_injective :
    Function.Injective m23SimplicityExtendHom := by
  intro g h hgh
  apply m23ExtendHom_injective
  have hPerm := congrArg
    (fun k : MulAction.stabilizer M24 (24 : Fin 24) =>
      ((k : M24) : Equiv.Perm (Fin 24))) hgh
  change m23ExtendHom g = m23ExtendHom h at hPerm
  exact hPerm

public theorem m23SimplicityExtendHom_bijective :
    Function.Bijective m23SimplicityExtendHom := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨m23SimplicityExtendHom_injective,
    Nat.card_congr m23EquivM24PointStabilizer⟩

/-- A pointwise-transparent copy of the M23--M24 point-stabilizer equivalence. -/
@[expose] public noncomputable def m23SimplicityExtendEquiv :
    M23 ≃* MulAction.stabilizer M24 (24 : Fin 24) :=
  MulEquiv.ofBijective m23SimplicityExtendHom
    m23SimplicityExtendHom_bijective

@[expose] public noncomputable def m23GeneratorAInM23 : M23 :=
  m23SimplicityExtendEquiv.symm m23M24StabilizerGeneratorA

@[expose] public noncomputable def m23GeneratorBInM23 : M23 :=
  m23SimplicityExtendEquiv.symm m23M24StabilizerGeneratorB

public theorem m23GeneratorA_extension :
    m23SimplicityExtendHom m23GeneratorAInM23 =
      m23M24StabilizerGeneratorA := by
  change m23SimplicityExtendEquiv
    (m23SimplicityExtendEquiv.symm m23M24StabilizerGeneratorA) = _
  exact m23SimplicityExtendEquiv.apply_symm_apply _

public theorem m23GeneratorB_extension :
    m23SimplicityExtendHom m23GeneratorBInM23 =
      m23M24StabilizerGeneratorB := by
  change m23SimplicityExtendEquiv
    (m23SimplicityExtendEquiv.symm m23M24StabilizerGeneratorB) = _
  exact m23SimplicityExtendEquiv.apply_symm_apply _

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open MulAction
open scoped Pointwise

private theorem m23_normalIntersection_eq_bot_or_eq_top
    (N : Subgroup M23) (hN : N.Normal) :
    N.comap (MulAction.stabilizer M23 (9 : Fin 23)).subtype = ⊥ ∨
      N.comap (MulAction.stabilizer M23 (9 : Fin 23)).subtype = ⊤ := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let : IsSimpleGroup (MulAction.stabilizer M23 (9 : Fin 23)) :=
    m23EquivM22PointStabilizer.symm.isSimpleGroup
  let : N.Normal := hN
  let :
      (N.comap (MulAction.stabilizer M23 (9 : Fin 23)).subtype).Normal :=
    hN.comap (MulAction.stabilizer M23 (9 : Fin 23)).subtype
  exact
    (inferInstance :
      (N.comap (MulAction.stabilizer M23 (9 : Fin 23)).subtype).Normal).eq_bot_or_eq_top

private theorem m23_no_regular_normal
    (N : Subgroup M23) (hN : N.Normal)
    [MulAction.IsPretransitive N (Fin 23)]
    (hcardN : Nat.card N = 23) : False := by
  classical
  let : Fact (Nat.Prime 23) := ⟨by decide +kernel⟩
  let : N.Normal := hN
  let H := MulAction.stabilizer M23 (9 : Fin 23)
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let : IsSimpleGroup H := m23EquivM22PointStabilizer.symm.isSimpleGroup
  let : IsCyclic N := isCyclic_of_prime_card hcardN
  let φ : H →* MulAut N :=
    (MulAut.conjNormal : M23 →* MulAut N).comp H.subtype
  have hHcard : Nat.card H = 443520 := m23PointStabilizerNine_card
  have hφ : φ = 1 :=
    MonoidHom.eq_one_of_isSimpleGroup_of_card_lt φ (by
      rw [IsCyclic.card_mulAut N, hcardN, hHcard,
        Nat.totient_prime (by decide +kernel)]
      norm_num)
  have hHidentity (h : H) : h = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨n, hn⟩ :=
      MulAction.exists_smul_eq N (9 : Fin 23) x
    have hn' : (n : M23) • (9 : Fin 23) = x := hn
    have hφh : φ h = 1 := by
      rw [hφ]
      rfl
    have happly := congrArg (fun e : MulAut N => e n) hφh
    have hval := congrArg (fun z : N => (z : M23)) happly
    change (h : M23) * (n : M23) * (h : M23)⁻¹ = (n : M23) at hval
    have hcomm : (h : M23) * (n : M23) = (n : M23) * (h : M23) := by
      calc
        (h : M23) * (n : M23) =
            ((h : M23) * (n : M23) * (h : M23)⁻¹) * (h : M23) := by
              simp [mul_assoc]
        _ = (n : M23) * (h : M23) := by rw [hval]
    change (h : M23) • x = x
    calc
      (h : M23) • x =
          (h : M23) • ((n : M23) • (9 : Fin 23)) := by rw [hn']
      _ = ((h : M23) * (n : M23)) • (9 : Fin 23) := by
        rw [mul_smul]
      _ = ((n : M23) * (h : M23)) • (9 : Fin 23) := by rw [hcomm]
      _ = (n : M23) • ((h : M23) • (9 : Fin 23)) := by
        rw [mul_smul]
      _ = (n : M23) • (9 : Fin 23) := by rw [h.property]
      _ = x := hn'
  let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hHcard]
    norm_num)
  obtain ⟨h, hh⟩ := exists_ne (1 : H)
  exact hh (hHidentity h)

/-- The Mathieu group M23 is simple. -/
public theorem m23_isSimpleGroup : IsSimpleGroup M23 := by
  classical
  let : MulAction.IsPreprimitive M23 (Fin 23) := m23_isPreprimitive
  let : Nontrivial M23 := Finite.one_lt_card_iff_nontrivial.mp (by
    have hmul := Subgroup.card_mul_index
      (MulAction.stabilizer M23 (9 : Fin 23))
    rw [m23PointStabilizerNine_card,
      MulAction.index_stabilizer_of_transitive M23 (9 : Fin 23),
      Nat.card_fin] at hmul
    omega)
  apply IsSimpleGroup.mk
  intro N hN
  let : N.Normal := hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  right
  have hfix : MulAction.fixedPoints N (Fin 23) ≠ Set.univ := by
    intro h
    apply hNbot
    apply N.eq_bot_iff_forall.mpr
    intro n hn
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have hx : x ∈ MulAction.fixedPoints N (Fin 23) := by
      rw [h]
      exact Set.mem_univ x
    have hxn := (MulAction.mem_fixedPoints.mp hx) ⟨n, hn⟩
    change (n : Equiv.Perm (Fin 23)) x = x at hxn
    exact hxn
  let : MulAction.IsPretransitive N (Fin 23) :=
    (inferInstance :
      MulAction.IsQuasiPreprimitive M23 (Fin 23)).isPretransitive_of_normal hfix
  rcases m23_normalIntersection_eq_bot_or_eq_top N hN with hKbot | hKtop
  · have hcardN : Nat.card N = 23 := by
      simpa using
        (MulAction.card_eq_card_of_comap_stabilizer_eq_bot N (9 : Fin 23) hKbot)
    exfalso
    exact m23_no_regular_normal N hN hcardN
  · have hHle : MulAction.stabilizer M23 (9 : Fin 23) ≤ N := by
      intro g hg
      let h : MulAction.stabilizer M23 (9 : Fin 23) := ⟨g, hg⟩
      have hh :
          h ∈ N.comap (MulAction.stabilizer M23 (9 : Fin 23)).subtype := by
        rw [hKtop]
        exact Subgroup.mem_top h
      exact hh
    exact MulAction.eq_top_of_stabilizer_le N (9 : Fin 23) hHle

end Sporadic.Mathieu
