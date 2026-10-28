module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.GroupTheory.GroupAction.Transitive
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FinCases
public import Theory.Mathieu.M11.Basic
public import Theory.Mathieu.M12.Basic

namespace Sporadic.Mathieu

set_option maxHeartbeats 800000
set_option maxRecDepth 100000


open scoped Pointwise

/-- Explicit values of the Atlas point embedding. -/
public def m11M12PointEmbeddingValue : Fin 11 -> Fin 12
  | 0 => 5
  | 1 => 1
  | 2 => 7
  | 3 => 8
  | 4 => 6
  | 5 => 4
  | 6 => 2
  | 7 => 3
  | 8 => 11
  | 9 => 9
  | 10 => 10
  | _ => 5

private def m11M12PointInv : Fin 12 -> Fin 11
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | 3 => 7
  | 4 => 5
  | 5 => 0
  | 6 => 4
  | 7 => 2
  | 8 => 3
  | 9 => 9
  | 10 => 10
  | 11 => 8
  | _ => 0

private theorem m11M12PointEmbeddingValue_left (i : Fin 11) :
    m11M12PointInv (m11M12PointEmbeddingValue i) = i := by
  fin_cases i <;> rfl

private theorem m11M12PointEmbeddingValue_right (x : Fin 12) (hx : x ≠ 0) :
    m11M12PointEmbeddingValue (m11M12PointInv x) = x := by
  fin_cases x <;> simp_all [m11M12PointEmbeddingValue, m11M12PointInv]

/-- The Atlas-labelled degree-11 points embedded in the degree-12 action. -/
public def m11M12PointEquiv :
    Fin 11 ≃ {x : Fin 12 // x ≠ (12 : Fin 12)} where
  toFun i := ⟨m11M12PointEmbeddingValue i, by fin_cases i <;> decide +kernel⟩
  invFun x := m11M12PointInv x.1
  left_inv := m11M12PointEmbeddingValue_left
  right_inv := by
    intro x
    apply Subtype.ext
    exact m11M12PointEmbeddingValue_right x.1 x.2

@[expose] public def m11M12PointEmbedding : Fin 11 ↪ Fin 12 :=
  m11M12PointEquiv.toEmbedding.trans (Function.Embedding.subtype _)

public theorem m11M12PointEmbedding_eq_value (i : Fin 11) :
    m11M12PointEmbedding i = m11M12PointEmbeddingValue i := by
    fin_cases i <;> rfl

/-- Extend an M11 automorphism by fixing the twelfth Atlas point. -/
public noncomputable def m11ToM12ExtendHom : M11 →* Equiv.Perm (Fin 12) :=
  (Equiv.Perm.viaEmbeddingHom m11M12PointEmbedding).comp M11.subtype

public theorem m11ToM12ExtendHom_injective :
    Function.Injective m11ToM12ExtendHom := by
  intro g h hgh
  apply Subtype.ext
  apply Equiv.Perm.viaEmbeddingHom_injective m11M12PointEmbedding
  simpa [m11ToM12ExtendHom] using hgh

public theorem m11ToM12ExtendHom_apply_embedded (g : M11) (i : Fin 11) :
    m11ToM12ExtendHom g (m11M12PointEmbedding i) =
      m11M12PointEmbedding ((g : Equiv.Perm (Fin 11)) i) := by
  simpa [m11ToM12ExtendHom, Equiv.Perm.viaEmbeddingHom_apply] using
    (Equiv.Perm.viaEmbedding_apply (e := (g : Equiv.Perm (Fin 11)))
      (ι := m11M12PointEmbedding) i)

public theorem m11ToM12ExtendHom_apply_12 (g : M11) :
    m11ToM12ExtendHom g (12 : Fin 12) = (12 : Fin 12) := by
  rw [m11ToM12ExtendHom, MonoidHom.comp_apply, Equiv.Perm.viaEmbeddingHom_apply]
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨x, hx⟩
  change (m11M12PointEquiv x).1 = (12 : Fin 12) at hx
  exact (m11M12PointEquiv x).2 hx

private def m11M12LiftBlock (B : Finset (Fin 11)) : Finset (Fin 12) :=
  B.map m11M12PointEmbedding

private def m11M12AugmentedBlock (B : Finset (Fin 11)) : Finset (Fin 12) :=
  insert (12 : Fin 12) (m11M12LiftBlock B)

private def m11M12ComplementBlock (B : Finset (Fin 11)) : Finset (Fin 12) :=
  (Finset.univ : Finset (Fin 12)) \ m11M12AugmentedBlock B

private noncomputable def m11M12ReconstructedBlocks : Finset (Finset (Fin 12)) :=
  m11Blocks.image m11M12AugmentedBlock ∪
    m11Blocks.image m11M12ComplementBlock

private def m12ReconstructionIndexArray : Array (Fin 66) :=
  #[32, 37, 52, 15, 35, 59, 27, 4, 44, 50, 40, 28, 57, 42, 25, 47, 20, 62, 7, 31,
    12, 34, 10, 49, 39, 65, 54, 23, 1, 18, 46, 8, 30, 56, 21, 61, 41, 26, 53, 24,
    48, 38, 19, 64, 13, 33, 2, 11, 36, 22, 60, 51, 17, 0, 55, 45, 9, 16, 63, 6,
    43, 3, 29, 5, 14, 58, 58, 14, 5, 29, 3, 43, 6, 63, 16, 9, 45, 55, 0, 17,
    51, 60, 22, 36, 11, 2, 33, 13, 64, 19, 38, 48, 24, 53, 26, 41, 61, 21, 56,
    30, 8, 46, 18, 1, 23, 54, 65, 39, 49, 10, 34, 12, 31, 7, 62, 20, 47, 25, 42,
    57, 28, 40, 50, 44, 4, 27, 59, 35, 15, 52, 37, 32]

private theorem m12ReconstructionIndexArray_size :
    m12ReconstructionIndexArray.size = 132 := by decide +kernel

private def m12ReconstructionIndex (i : Fin 132) : Fin 66 :=
  m12ReconstructionIndexArray[i.val]'(by
    simp [m12ReconstructionIndexArray_size])

private def m12ReconstructionComplementArray : Array Bool :=
  #[true, true, true, false, true, true, false, false, true, true, true, false, true, true,
    false, true, false, true, false, true, false, true, false, true, true, true, true, false,
    false, false, true, false, true, true, false, true, true, false, true, false, true, true,
    false, true, false, true, false, false, true, false, true, true, false, false, true, true,
    false, false, true, false, true, false, false, false, false, true, false, true, true, true,
    true, false, true, false, true, true, false, false, true, true, false, false, true, false,
    true, true, false, true, false, true, false, false, true, false, true, false, false, true,
    false, false, true, false, true, true, true, false, false, false, false, true, false, true,
    false, true, false, true, false, true, false, false, true, false, false, false, true, true,
    false, false, true, false, false, false]

private theorem m12ReconstructionComplementArray_size :
    m12ReconstructionComplementArray.size = 132 := by decide +kernel

private def m12ReconstructionComplement (i : Fin 132) : Bool :=
  m12ReconstructionComplementArray[i.val]'(by
    simp [m12ReconstructionComplementArray_size])

private theorem m12BlockAt_reconstruction_mem (i : Fin 132) (x : Fin 12) :
    x ∈ m12BlockAt i ↔
      x ∈ (if m12ReconstructionComplement i then
        m11M12ComplementBlock (m11BlockAt (m12ReconstructionIndex i))
      else
        m11M12AugmentedBlock (m11BlockAt (m12ReconstructionIndex i))) := by
  revert i x
  decide +kernel

private theorem m12BlockAt_reconstruction (i : Fin 132) :
    m12BlockAt i =
      if m12ReconstructionComplement i then
        m11M12ComplementBlock (m11BlockAt (m12ReconstructionIndex i))
      else
        m11M12AugmentedBlock (m11BlockAt (m12ReconstructionIndex i)) := by
  ext x
  exact m12BlockAt_reconstruction_mem i x

private def m12ReconstructionAugIndex : Fin 66 → Fin 132 :=
  ![
    53, 28, 46, 61, 7, 63, 59, 18, 31, 56, 22, 47,
    20, 44, 64, 3, 57, 52, 29, 42, 16, 34, 49, 27,
    39, 14, 37, 6, 11, 62, 99, 112, 131, 86, 110, 127,
    83, 130, 90, 107, 121, 95, 118, 71, 123, 76, 101, 116,
    91, 108, 122, 80, 129, 93, 105, 77, 98, 119, 66, 126,
    81, 96, 114, 73, 88, 106
  ]

private theorem m12ReconstructionAugIndex_right (j : Fin 66) :
    m12ReconstructionIndex (m12ReconstructionAugIndex j) = j ∧
      m12ReconstructionComplement (m12ReconstructionAugIndex j) = false := by
  revert j
  decide +kernel

private theorem m12Reconstruction_aug_surj (j : Fin 66) :
    ∃ i : Fin 132,
      m12ReconstructionIndex i = j ∧ m12ReconstructionComplement i = false :=
  ⟨m12ReconstructionAugIndex j, m12ReconstructionAugIndex_right j⟩

private def m12ReconstructionCompIndex : Fin 66 → Fin 132 :=
  ![
    78, 103, 85, 70, 124, 68, 72, 113, 100, 75, 109, 84,
    111, 87, 67, 128, 74, 79, 102, 89, 115, 97, 82, 104,
    92, 117, 94, 125, 120, 69, 32, 19, 0, 45, 21, 4,
    48, 1, 41, 24, 10, 36, 13, 60, 8, 55, 30, 15,
    40, 23, 9, 51, 2, 38, 26, 54, 33, 12, 65, 5,
    50, 35, 17, 58, 43, 25
  ]

private theorem m12ReconstructionCompIndex_right (j : Fin 66) :
    m12ReconstructionIndex (m12ReconstructionCompIndex j) = j ∧
      m12ReconstructionComplement (m12ReconstructionCompIndex j) = true := by
  revert j
  decide +kernel

private theorem m12Reconstruction_comp_surj (j : Fin 66) :
    ∃ i : Fin 132,
      m12ReconstructionIndex i = j ∧ m12ReconstructionComplement i = true :=
  ⟨m12ReconstructionCompIndex j, m12ReconstructionCompIndex_right j⟩
private theorem m12Blocks_eq_m11Reconstruction :
    m12Blocks = m11M12ReconstructedBlocks := by
  rw [← m12BlockAt_image]
  apply Finset.Subset.antisymm
  · intro B hB
    rcases Finset.mem_image.mp hB with ⟨i, -, rfl⟩
    rw [m12BlockAt_reconstruction]
    cases h : m12ReconstructionComplement i
    · change m11M12AugmentedBlock (m11BlockAt (m12ReconstructionIndex i)) ∈ m11M12ReconstructedBlocks
      rw [m11M12ReconstructedBlocks, Finset.mem_union]
      left
      apply Finset.mem_image.mpr
      refine ⟨m11BlockAt (m12ReconstructionIndex i), ?_, rfl⟩
      rw [m11Blocks]
      exact Finset.mem_image.mpr ⟨m12ReconstructionIndex i, Finset.mem_univ _, rfl⟩
    · change m11M12ComplementBlock (m11BlockAt (m12ReconstructionIndex i)) ∈ m11M12ReconstructedBlocks
      rw [m11M12ReconstructedBlocks, Finset.mem_union]
      right
      apply Finset.mem_image.mpr
      refine ⟨m11BlockAt (m12ReconstructionIndex i), ?_, rfl⟩
      rw [m11Blocks]
      exact Finset.mem_image.mpr ⟨m12ReconstructionIndex i, Finset.mem_univ _, rfl⟩
  · intro B hB
    rw [m11M12ReconstructedBlocks, Finset.mem_union] at hB
    rcases hB with hAug | hComp
    · rcases Finset.mem_image.mp hAug with ⟨C, hC, rfl⟩
      rw [m11Blocks] at hC
      rcases Finset.mem_image.mp hC with ⟨j, -, rfl⟩
      obtain ⟨i, hi, hflag⟩ := m12Reconstruction_aug_surj j
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      simpa [hflag, hi] using (m12BlockAt_reconstruction i)
    · rcases Finset.mem_image.mp hComp with ⟨C, hC, rfl⟩
      rw [m11Blocks] at hC
      rcases Finset.mem_image.mp hC with ⟨j, -, rfl⟩
      obtain ⟨i, hi, hflag⟩ := m12Reconstruction_comp_surj j
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      simpa [hflag, hi] using (m12BlockAt_reconstruction i)

private theorem m11_smul_blocks (g : M11) :
    (g : Equiv.Perm (Fin 11)) • m11Blocks = m11Blocks := by
  apply Finset.coe_injective
  simpa only [Finset.coe_smul_finset] using
    (mem_M11_iff (g : Equiv.Perm (Fin 11))).mp g.property

private theorem m11ToM12ExtendHom_smul_liftBlock
    (g : M11) (B : Finset (Fin 11)) :
    m11ToM12ExtendHom g • m11M12LiftBlock B =
      m11M12LiftBlock ((g : Equiv.Perm (Fin 11)) • B) := by
  ext x
  simp [m11M12LiftBlock, Finset.mem_smul_finset,
    m11ToM12ExtendHom_apply_embedded]

private theorem m11ToM12ExtendHom_smul_augmentedBlock
    (g : M11) (B : Finset (Fin 11)) :
    m11ToM12ExtendHom g • m11M12AugmentedBlock B =
      m11M12AugmentedBlock ((g : Equiv.Perm (Fin 11)) • B) := by
  rw [m11M12AugmentedBlock, m11M12AugmentedBlock, Finset.smul_finset_insert]
  change
    insert (m11ToM12ExtendHom g (12 : Fin 12))
        (m11ToM12ExtendHom g • m11M12LiftBlock B) =
      insert (12 : Fin 12)
        (m11M12LiftBlock ((g : Equiv.Perm (Fin 11)) • B))
  rw [m11ToM12ExtendHom_apply_12, m11ToM12ExtendHom_smul_liftBlock]

private theorem m11ToM12ExtendHom_smul_complementBlock
    (g : M11) (B : Finset (Fin 11)) :
    m11ToM12ExtendHom g • m11M12ComplementBlock B =
      m11M12ComplementBlock ((g : Equiv.Perm (Fin 11)) • B) := by
  rw [m11M12ComplementBlock, m11M12ComplementBlock,
    Finset.smul_finset_sdiff, Finset.smul_finset_univ,
    m11ToM12ExtendHom_smul_augmentedBlock]

private theorem m11ToM12ExtendHom_smul_reconstructedBlocks (g : M11) :
    m11ToM12ExtendHom g • m11M12ReconstructedBlocks =
      m11M12ReconstructedBlocks := by
  apply Finset.eq_of_subset_of_card_le
  · intro C hC
    rcases Finset.mem_smul_finset.mp hC with ⟨D, hD, rfl⟩
    rw [m11M12ReconstructedBlocks, Finset.mem_union] at hD ⊢
    rcases hD with hAug | hComp
    · rcases Finset.mem_image.mp hAug with ⟨B, hB, rfl⟩
      left
      rw [m11ToM12ExtendHom_smul_augmentedBlock]
      apply Finset.mem_image.mpr
      refine ⟨(g : Equiv.Perm (Fin 11)) • B, ?_, rfl⟩
      rw [← m11_smul_blocks g]
      exact Finset.smul_mem_smul_finset hB
    · rcases Finset.mem_image.mp hComp with ⟨B, hB, rfl⟩
      right
      rw [m11ToM12ExtendHom_smul_complementBlock]
      apply Finset.mem_image.mpr
      refine ⟨(g : Equiv.Perm (Fin 11)) • B, ?_, rfl⟩
      rw [← m11_smul_blocks g]
      exact Finset.smul_mem_smul_finset hB
  · simp

/-- Extend M11 into the M12 automorphism group. -/
public theorem m11ToM12Extend_mem_M12 (g : M11) :
    m11ToM12ExtendHom g ∈ M12 := by
  rw [mem_M12_iff]
  have hFinset : m11ToM12ExtendHom g • m12Blocks = m12Blocks := by
    rw [m12Blocks_eq_m11Reconstruction]
    exact m11ToM12ExtendHom_smul_reconstructedBlocks g
  simpa only [Finset.coe_smul_finset] using
    congrArg (fun s : Finset (Finset (Fin 12)) => (s : Set (Finset (Fin 12)))) hFinset

/-- Extend M11 into the M12 point stabilizer. -/
@[expose] public noncomputable def m11ToM12PointStabilizer :
    M11 →* MulAction.stabilizer M12 (12 : Fin 12) :=
  (m11ToM12ExtendHom.codRestrict M12 (fun g => m11ToM12Extend_mem_M12 g)).codRestrict
    (MulAction.stabilizer M12 (12 : Fin 12)) (fun g => by
      rw [MulAction.mem_stabilizer_iff]
      exact m11ToM12ExtendHom_apply_12 g)

public theorem m11ToM12PointStabilizer_injective :
    Function.Injective m11ToM12PointStabilizer := by
  intro g h hgh
  apply m11ToM12ExtendHom_injective
  have hPerm := congrArg
    (fun k : MulAction.stabilizer M12 (12 : Fin 12) =>
      ((k : M12) : Equiv.Perm (Fin 12))) hgh
  change m11ToM12ExtendHom g = m11ToM12ExtendHom h at hPerm
  exact hPerm

private theorem m12PointStabilizer_smul_blocks
    (g : MulAction.stabilizer M12 (12 : Fin 12)) :
    ((g : M12) : Equiv.Perm (Fin 12)) • m12Blocks = m12Blocks := by
  have hg := (mem_M12_iff ((g : M12) : Equiv.Perm (Fin 12))).mp
    (g : M12).property
  apply Finset.coe_injective
  simpa only [Finset.coe_smul_finset] using hg

private noncomputable def m12PointStabilizerComplementHom :
    MulAction.stabilizer M12 (12 : Fin 12) →*
      Equiv.Perm {x : Fin 12 // x ≠ (12 : Fin 12)} where
  toFun g :=
    ((g : M12) : Equiv.Perm (Fin 12)).subtypePerm
      (fun x => by
        have hfix : ((g : M12) : Equiv.Perm (Fin 12)) (12 : Fin 12) =
            (12 : Fin 12) := by
          change (g : M12) • (12 : Fin 12) = (12 : Fin 12)
          exact g.property
        simpa only [hfix] using
          not_congr (((g : M12) : Equiv.Perm (Fin 12)).injective.eq_iff :
            ((g : M12) : Equiv.Perm (Fin 12)) x =
              ((g : M12) : Equiv.Perm (Fin 12)) (12 : Fin 12) ↔
              x = (12 : Fin 12)))
  map_one' := by
    ext x
    rfl
  map_mul' g h := by
    ext x
    rfl

private noncomputable def m12PointStabilizerRestrictHom :
    MulAction.stabilizer M12 (12 : Fin 12) →* Equiv.Perm (Fin 11) :=
  m11M12PointEquiv.symm.permCongrHom.toMonoidHom.comp
    m12PointStabilizerComplementHom

private theorem m12PointStabilizerRestrictHom_apply
    (g : MulAction.stabilizer M12 (12 : Fin 12)) (i : Fin 11) :
    m11M12PointEmbedding (m12PointStabilizerRestrictHom g i) =
      ((g : M12) : Equiv.Perm (Fin 12)) (m11M12PointEmbedding i) := by
  change
    (m11M12PointEquiv
      (m11M12PointEquiv.symm.permCongr
        (m12PointStabilizerComplementHom g) i)).1 =
      ((g : M12) : Equiv.Perm (Fin 12)) (m11M12PointEmbedding i)
  rw [Equiv.permCongr_apply, m11M12PointEquiv.apply_symm_apply]
  rfl

private theorem m11M12LiftBlock_not_mem_12 (B : Finset (Fin 11)) :
    (12 : Fin 12) ∉ m11M12LiftBlock B := by
  rw [m11M12LiftBlock, Finset.mem_map]
  rintro ⟨x, -, hx⟩
  change (m11M12PointEquiv x).1 = (12 : Fin 12) at hx
  exact (m11M12PointEquiv x).2 hx
private theorem m11M12AugmentedBlock_injective :
    Function.Injective m11M12AugmentedBlock := by
  intro B C hBC
  have hErase := congrArg
    (fun S : Finset (Fin 12) => S.erase (12 : Fin 12)) hBC
  rw [m11M12AugmentedBlock, Finset.erase_insert (m11M12LiftBlock_not_mem_12 B)] at hErase
  rw [m11M12AugmentedBlock, Finset.erase_insert (m11M12LiftBlock_not_mem_12 C)] at hErase
  exact Finset.map_injective m11M12PointEmbedding (by
    simpa [m11M12LiftBlock] using hErase)

private theorem m12Blocks_through_12 :
    m12Blocks.filter (fun B => (12 : Fin 12) ∈ B) =
      m11Blocks.image m11M12AugmentedBlock := by
  rw [m12Blocks_eq_m11Reconstruction]
  ext B
  constructor
  · intro hB
    rcases Finset.mem_filter.mp hB with ⟨hMem, hThrough⟩
    change B ∈ m11Blocks.image m11M12AugmentedBlock ∪
      m11Blocks.image m11M12ComplementBlock at hMem
    rcases Finset.mem_union.mp hMem with hAug | hComp
    · exact hAug
    · rcases Finset.mem_image.mp hComp with ⟨C, hC, rfl⟩
      simp [m11M12ComplementBlock, m11M12AugmentedBlock] at hThrough
  · intro hB
    apply Finset.mem_filter.mpr
    constructor
    · rw [m11M12ReconstructedBlocks, Finset.mem_union]
      exact Or.inl hB
    · rcases Finset.mem_image.mp hB with ⟨C, hC, rfl⟩
      simp [m11M12AugmentedBlock]

private theorem m12PointStabilizer_smul_liftBlock
    (g : MulAction.stabilizer M12 (12 : Fin 12)) (B : Finset (Fin 11)) :
    ((g : M12) : Equiv.Perm (Fin 12)) • m11M12LiftBlock B =
      m11M12LiftBlock (m12PointStabilizerRestrictHom g • B) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_smul_finset.mp hx with ⟨y, hy, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨a, ha, rfl⟩
    rw [m11M12LiftBlock, Finset.mem_map]
    exact ⟨m12PointStabilizerRestrictHom g a,
      Finset.smul_mem_smul_finset ha,
      m12PointStabilizerRestrictHom_apply g a⟩
  · intro hx
    rw [m11M12LiftBlock] at hx
    rcases Finset.mem_map.mp hx with ⟨a, ha, hax⟩
    rcases Finset.mem_smul_finset.mp ha with ⟨b, hb, rfl⟩
    apply Finset.mem_smul_finset.mpr
    refine ⟨m11M12PointEmbedding b, Finset.mem_map.mpr ⟨b, hb, rfl⟩, ?_⟩
    change ((g : M12) : Equiv.Perm (Fin 12)) (m11M12PointEmbedding b) = x
    rw [← m12PointStabilizerRestrictHom_apply g b]
    exact hax

private theorem m12PointStabilizer_smul_augmentedBlock
    (g : MulAction.stabilizer M12 (12 : Fin 12)) (B : Finset (Fin 11)) :
    ((g : M12) : Equiv.Perm (Fin 12)) • m11M12AugmentedBlock B =
      m11M12AugmentedBlock (m12PointStabilizerRestrictHom g • B) := by
  rw [m11M12AugmentedBlock, m11M12AugmentedBlock, Finset.smul_finset_insert]
  change
    insert (((g : M12) : Equiv.Perm (Fin 12)) (12 : Fin 12))
        (((g : M12) : Equiv.Perm (Fin 12)) • m11M12LiftBlock B) =
      insert (12 : Fin 12)
        (m11M12LiftBlock (m12PointStabilizerRestrictHom g • B))
  have hfix : ((g : M12) : Equiv.Perm (Fin 12)) (12 : Fin 12) = (12 : Fin 12) := by
    change (g : M12) • (12 : Fin 12) = (12 : Fin 12)
    exact g.property
  rw [hfix, m12PointStabilizer_smul_liftBlock]

private theorem m12PointStabilizer_smul_m11Blocks
    (g : MulAction.stabilizer M12 (12 : Fin 12)) :
    (m12PointStabilizerRestrictHom g) • m11Blocks = m11Blocks := by
  apply Finset.eq_of_subset_of_card_le
  · intro C hC
    rcases Finset.mem_smul_finset.mp hC with ⟨B, hB, rfl⟩
    have hAug : m11M12AugmentedBlock B ∈ m12Blocks := by
      rw [m12Blocks_eq_m11Reconstruction, m11M12ReconstructedBlocks]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨B, hB, rfl⟩)
    have hImage := Finset.smul_mem_smul_finset (a := ((g : M12) : Equiv.Perm (Fin 12))) (s := m12Blocks) (b := m11M12AugmentedBlock B) hAug
    rw [m12PointStabilizer_smul_blocks] at hImage
    have hThrough : ((g : M12) : Equiv.Perm (Fin 12)) •
        m11M12AugmentedBlock B ∈ m12Blocks.filter
          (fun C => (12 : Fin 12) ∈ C) := by
      apply Finset.mem_filter.mpr
      constructor
      · exact hImage
      · apply Finset.mem_smul_finset.mpr
        refine ⟨(12 : Fin 12), by simp [m11M12AugmentedBlock], ?_⟩
        exact g.property
    rw [m12Blocks_through_12] at hThrough
    rcases Finset.mem_image.mp hThrough with ⟨D, hD, hEq⟩
    have hEq' : m11M12AugmentedBlock D =
        m11M12AugmentedBlock (m12PointStabilizerRestrictHom g • B) :=
      hEq.trans (m12PointStabilizer_smul_augmentedBlock g B)
    have hDB : D = m12PointStabilizerRestrictHom g • B :=
      m11M12AugmentedBlock_injective hEq'
    simpa [hDB] using hD
  · simp

private theorem m12PointStabilizerRestrictHom_mem_M11
    (g : MulAction.stabilizer M12 (12 : Fin 12)) :
    m12PointStabilizerRestrictHom g ∈ M11 := by
  rw [mem_M11_iff]
  simpa only [Finset.coe_smul_finset] using
    congrArg
      (fun s : Finset (Finset (Fin 11)) => (s : Set (Finset (Fin 11))))
      (m12PointStabilizer_smul_m11Blocks g)

private noncomputable def m12PointStabilizerToM11 :
    MulAction.stabilizer M12 (12 : Fin 12) →* M11 :=
  m12PointStabilizerRestrictHom.codRestrict M11
    (fun g => m12PointStabilizerRestrictHom_mem_M11 g)

private theorem m12PointStabilizerToM11_m11ToM12PointStabilizer (g : M11) :
    m12PointStabilizerToM11 (m11ToM12PointStabilizer g) = g := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply m11M12PointEmbedding.injective
  change m11M12PointEmbedding
      (m12PointStabilizerRestrictHom (m11ToM12PointStabilizer g) i) =
    m11M12PointEmbedding ((g : Equiv.Perm (Fin 11)) i)
  rw [m12PointStabilizerRestrictHom_apply]
  change m11ToM12ExtendHom g (m11M12PointEmbedding i) =
    m11M12PointEmbedding ((g : Equiv.Perm (Fin 11)) i)
  exact m11ToM12ExtendHom_apply_embedded g i

private theorem m11ToM12PointStabilizer_m12PointStabilizerToM11
    (g : MulAction.stabilizer M12 (12 : Fin 12)) :
    m11ToM12PointStabilizer (m12PointStabilizerToM11 g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : x = (12 : Fin 12)
  · subst x
    change m11ToM12ExtendHom (m12PointStabilizerToM11 g) (12 : Fin 12) =
      ((g : M12) : Equiv.Perm (Fin 12)) (12 : Fin 12)
    rw [m11ToM12ExtendHom_apply_12]
    exact g.property.symm
  · obtain ⟨i, hi⟩ := m11M12PointEquiv.surjective ⟨x, hx⟩
    have hEmbedding : m11M12PointEmbedding i = x := by
      change (m11M12PointEquiv i).1 = x
      exact congrArg Subtype.val hi
    rw [← hEmbedding]
    change m11ToM12ExtendHom (m12PointStabilizerToM11 g)
        (m11M12PointEmbedding i) =
      ((g : M12) : Equiv.Perm (Fin 12)) (m11M12PointEmbedding i)
    rw [m11ToM12ExtendHom_apply_embedded]
    exact m12PointStabilizerRestrictHom_apply g i

/-- The M11 design automorphism group is the point stabilizer in M12. -/
public noncomputable def m11EquivM12PointStabilizer :
    M11 ≃* MulAction.stabilizer M12 (12 : Fin 12) where
  toFun := m11ToM12PointStabilizer
  invFun := m12PointStabilizerToM11
  left_inv := m12PointStabilizerToM11_m11ToM12PointStabilizer
  right_inv := m11ToM12PointStabilizer_m12PointStabilizerToM11
  map_mul' := m11ToM12PointStabilizer.map_mul

/-- The M12 action on its twelve points is transitive. -/
public noncomputable instance : MulAction.IsPretransitive M12 (Fin 12) where
  exists_smul_eq := by
    let c : Equiv.Perm (Fin 12) := m12GeneratorA * m12GeneratorB
    let reps : Fin 12 -> Equiv.Perm (Fin 12)
      | 0 => 1
      | 1 => c ^ 4
      | 2 => c ^ 8
      | 3 => c ^ 3
      | 4 => c ^ 7
      | 5 => c
      | 6 => c ^ 2
      | 7 => c ^ 10
      | 8 => c ^ 5
      | 9 => c ^ 6
      | 10 => c ^ 9
      | 11 => m12GeneratorB
      | _ => 1
    have hc : c ∈ M12 := by
      exact M12.mul_mem m12GeneratorA_mem m12GeneratorB_mem
    have hMem : ∀ y : Fin 12, reps y ∈ M12 := by
      intro y
      simp only [reps]
      fin_cases y
      · exact M12.one_mem
      · exact M12.pow_mem hc _
      · exact M12.pow_mem hc _
      · exact M12.pow_mem hc _
      · exact M12.pow_mem hc _
      · exact hc
      · exact M12.pow_mem hc _
      · exact M12.pow_mem hc _
      · exact M12.pow_mem hc _
      · exact M12.pow_mem hc _
      · exact M12.pow_mem hc _
      · exact m12GeneratorB_mem
    have hOrbit : ∀ y : Fin 12, reps y • (0 : Fin 12) = y := by
      decide +kernel
    intro x y
    refine ⟨⟨reps y * (reps x)⁻¹,
      M12.mul_mem (hMem y) (M12.inv_mem (hMem x))⟩, ?_⟩
    calc
      (reps y * (reps x)⁻¹) • x =
          (reps y * (reps x)⁻¹) • (reps x • (0 : Fin 12)) := by
            rw [hOrbit x]
      _ = reps y • (0 : Fin 12) := by simp [mul_smul]
      _ = y := hOrbit y

end Sporadic.Mathieu
