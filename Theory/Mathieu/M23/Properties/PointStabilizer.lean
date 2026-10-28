module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Theory.Mathieu.M24.Basic
public import Theory.Mathieu.M23.Block
public import Theory.Mathieu.M23.Basic

open Theory.GroupTheory

namespace Sporadic.Mathieu

set_option linter.constructorNameAsVariable false

/-!
# The M23 extension into the M24 point stabilizer

This module proves the separate identification required by GLS Table 5.3d:
the automorphism group of the derived W23 design is the stabilizer of Atlas
point 24 in the W24 automorphism group.  The label-preserving point equivalence
omits Atlas point 24, represented by `0 : Fin 24`, and Mathlib's permutation
extension transports W23 automorphisms to that point stabilizer.
-/


open scoped Pointwise symmDiff

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- Extend a W23 permutation to `Fin 24` by fixing Atlas point 24. -/
public noncomputable def m23ExtendHom : M23 →* Equiv.Perm (Fin 24) :=
  (Equiv.Perm.viaEmbeddingHom m23PointEmbedding).comp M23.subtype

/-- Extension along `m23PointEmbedding` is injective. -/
public theorem m23ExtendHom_injective : Function.Injective m23ExtendHom := by
  intro g h hgh
  apply Subtype.ext
  apply Equiv.Perm.viaEmbeddingHom_injective m23PointEmbedding
  simpa [m23ExtendHom] using hgh

/-- The extension acts on embedded Atlas points 1--23 by the original permutation. -/
public theorem m23ExtendHom_apply_embedded (g : M23) (i : Fin 23) :
    m23ExtendHom g (m23PointEmbedding i) =
      m23PointEmbedding ((g : Equiv.Perm (Fin 23)) i) := by
  simpa [m23ExtendHom, Equiv.Perm.viaEmbeddingHom_apply] using
    (Equiv.Perm.viaEmbedding_apply (e := (g : Equiv.Perm (Fin 23)))
      (ι := m23PointEmbedding) i)

/-- The extension fixes Atlas point 24, represented by `0 : Fin 24`. -/
public theorem m23ExtendHom_apply_24 (g : M23) :
    m23ExtendHom g (24 : Fin 24) = (24 : Fin 24) := by
  rw [m23ExtendHom, MonoidHom.comp_apply, Equiv.Perm.viaEmbeddingHom_apply]
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨x, hx⟩
  change (m23PointEquiv x).1 = (24 : Fin 24) at hx
  exact (m23PointEquiv x).2 hx
/-- Lift the symmetric difference of a pair of W23 heptads. -/
private def m23SymmDiffBlock (p : Finset (Fin 23) × Finset (Fin 23)) : Finset (Fin 24) :=
  m23LiftBlock p.1 ∆ m23LiftBlock p.2

/-- Reconstruct W24 from the derived W23 design. -/
private noncomputable def m23ReconstructedBlocks : Finset (Finset (Fin 24)) :=
  m23Blocks.image m23AugmentedBlock ∪
    ((m23Blocks.product m23Blocks).filter (fun p => (p.1 ∩ p.2).card = 3)).image
      m23SymmDiffBlock

private theorem m23AugmentedBlock_injective :
    Function.Injective m23AugmentedBlock := by
  intro B C hBC
  have hErase := congrArg
    (fun S : Finset (Fin 24) => S.erase (24 : Fin 24)) hBC
  rw [m23AugmentedBlock, Finset.erase_insert (m23LiftBlock_not_mem_24 B)] at hErase
  rw [m23AugmentedBlock, Finset.erase_insert (m23LiftBlock_not_mem_24 C)] at hErase
  exact Finset.map_injective m23PointEmbedding (by
    simpa [m23LiftBlock] using hErase)

private theorem steinerSystem_card_filter_mem_mul_choose
    {α : Type*} [Fintype α] [DecidableEq α] {t k : ℕ}
    (D : SteinerSystem α t k) (p : α) (ht : 0 < t) :
    (D.blocks.filter (fun B => p ∈ B)).card *
        Nat.choose (k - 1) (t - 1) =
      Nat.choose (Fintype.card α - 1) (t - 1) := by
  let through := D.blocks.filter (fun B => p ∈ B)
  have hDisjoint :
      (through : Set (Finset α)).PairwiseDisjoint
        (fun B => (B.erase p).powersetCard (t - 1)) := by
    intro B₁ hB₁ B₂ hB₂ hne
    change Disjoint
      ((B₁.erase p).powersetCard (t - 1))
      ((B₂.erase p).powersetCard (t - 1))
    rw [Finset.disjoint_left]
    intro S hS₁ hS₂
    have hS₁Data := Finset.mem_powersetCard.mp hS₁
    have hS₂Data := Finset.mem_powersetCard.mp hS₂
    have hpS : p ∉ S := by
      intro hp
      exact (Finset.mem_erase.mp (hS₁Data.1 hp)).1 rfl
    have hInsertCard : (insert p S).card = t := by
      rw [Finset.card_insert_of_notMem hpS, hS₁Data.2]
      omega
    have hB₁Data := Finset.mem_filter.mp hB₁
    have hB₂Data := Finset.mem_filter.mp hB₂
    have hInsertSub₁ : insert p S ⊆ B₁ :=
      Finset.insert_subset hB₁Data.2 fun _ hx =>
        (Finset.mem_erase.mp (hS₁Data.1 hx)).2
    have hInsertSub₂ : insert p S ⊆ B₂ :=
      Finset.insert_subset hB₂Data.2 fun _ hx =>
        (Finset.mem_erase.mp (hS₂Data.1 hx)).2
    have hB₁Unique :
        B₁ ∈ D.blocks.filter (fun B => insert p S ⊆ B) :=
      Finset.mem_filter.mpr ⟨hB₁Data.1, hInsertSub₁⟩
    have hB₂Unique :
        B₂ ∈ D.blocks.filter (fun B => insert p S ⊆ B) :=
      Finset.mem_filter.mpr ⟨hB₂Data.1, hInsertSub₂⟩
    have hUnique := D.steiner (insert p S) hInsertCard
    apply hne
    exact (Finset.card_le_one_iff.mp (by omega)) hB₁Unique hB₂Unique
  have hCover :
      through.biUnion (fun B => (B.erase p).powersetCard (t - 1)) =
        ((Finset.univ : Finset α).erase p).powersetCard (t - 1) := by
    ext S
    constructor
    · intro hS
      rcases Finset.mem_biUnion.mp hS with ⟨B, hB, hSPower⟩
      have hSData := Finset.mem_powersetCard.mp hSPower
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_erase.mpr ⟨Finset.subset_univ S, ?_⟩, hSData.2⟩
      intro hp
      exact (Finset.mem_erase.mp (hSData.1 hp)).1 rfl
    · intro hS
      have hSData := Finset.mem_powersetCard.mp hS
      have hpS : p ∉ S := (Finset.subset_erase.mp hSData.1).2
      have hInsertCard : (insert p S).card = t := by
        rw [Finset.card_insert_of_notMem hpS, hSData.2]
        omega
      have hUnique := D.steiner (insert p S) hInsertCard
      obtain ⟨B, hBsingle⟩ := Finset.card_eq_one.mp hUnique
      have hBfilter :
          B ∈ D.blocks.filter (fun C => insert p S ⊆ C) := by
        rw [hBsingle]
        simp
      have hBData := Finset.mem_filter.mp hBfilter
      apply Finset.mem_biUnion.mpr
      refine ⟨B, Finset.mem_filter.mpr
        ⟨hBData.1, hBData.2 (Finset.mem_insert_self _ _)⟩, ?_⟩
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_erase.mpr ⟨?_, hpS⟩, hSData.2⟩
      intro x hx
      exact hBData.2 (Finset.mem_insert_of_mem hx)
  have hEraseCard :
      ∀ B ∈ through, (B.erase p).card = k - 1 := by
    intro B hB
    have hBData := Finset.mem_filter.mp hB
    rw [Finset.card_erase_of_mem hBData.2, D.block_card B hBData.1]
  have hCard := congrArg Finset.card hCover
  rw [Finset.card_biUnion hDisjoint] at hCard
  simp_rw [Finset.card_powersetCard] at hCard
  rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ] at hCard
  change through.card * Nat.choose (k - 1) (t - 1) =
    Nat.choose (Fintype.card α - 1) (t - 1)
  calc
    through.card * Nat.choose (k - 1) (t - 1) =
        ∑ _B ∈ through, Nat.choose (k - 1) (t - 1) := by simp
    _ = ∑ B ∈ through, Nat.choose (B.erase p).card (t - 1) := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [hEraseCard B hB]
    _ = Nat.choose (Fintype.card α - 1) (t - 1) := hCard
private theorem m24Blocks_through_24_card :
    (m24Blocks.filter (fun B => (24 : Fin 24) ∈ B)).card = 253 := by
  let D : SteinerSystem (Fin 24) 5 8 := {
    blocks := m24Blocks
    block_card := m24Blocks_card
    steiner := m24Blocks_unique_block
  }
  have h := steinerSystem_card_filter_mem_mul_choose
    D (24 : Fin 24) (by decide +kernel)
  change (m24Blocks.filter (fun B => (24 : Fin 24) ∈ B)).card *
    Nat.choose 7 4 = Nat.choose 23 4 at h
  have hChoose74 : Nat.choose 7 4 = 35 := by decide +kernel
  have hChoose234 : Nat.choose 23 4 = 8855 := by decide +kernel
  rw [hChoose74, hChoose234] at h
  omega

private theorem m24Blocks_through_24 :
    m24Blocks.filter (fun B => (24 : Fin 24) ∈ B) =
      m23Blocks.image m23AugmentedBlock := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨B, hB, rfl⟩
    rw [m23Blocks] at hB
    rcases Finset.mem_image.mp hB with ⟨i, -, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · rw [m23AugmentedBlockAt_eq_m24BlockAt, m24Blocks]
      exact Finset.mem_image.mpr
        ⟨m23BlockM24Index i, Finset.mem_univ _, rfl⟩
    · simp [m23AugmentedBlock]
  · rw [m24Blocks_through_24_card,
      Finset.card_image_of_injective _ m23AugmentedBlock_injective,
      m23BlocksCardinalityCheck]

private theorem m23AugmentedBlock_mem_m24Blocks
    (B : Finset (Fin 23)) (hB : B ∈ m23Blocks) :
    m23AugmentedBlock B ∈ m24Blocks := by
  have hImage :
      m23AugmentedBlock B ∈ m23Blocks.image m23AugmentedBlock :=
    Finset.mem_image.mpr ⟨B, hB, rfl⟩
  rw [← m24Blocks_through_24] at hImage
  exact (Finset.mem_filter.mp hImage).1

private theorem m23AugmentedBlock_symmDiff
    (B C : Finset (Fin 23)) :
    m23AugmentedBlock B ∆ m23AugmentedBlock C =
      m23LiftBlock B ∆ m23LiftBlock C := by
  have hB0 : (0 : Fin 24) ∉ m23LiftBlock B := by
    simpa using m23LiftBlock_not_mem_24 B
  have hC0 : (0 : Fin 24) ∉ m23LiftBlock C := by
    simpa using m23LiftBlock_not_mem_24 C
  ext x
  by_cases hx : x = (0 : Fin 24)
  · subst x
    simp [m23AugmentedBlock, Finset.mem_symmDiff, hB0, hC0]
  · simp [m23AugmentedBlock, Finset.mem_symmDiff, hx]

private theorem m24Blocks_symmDiff_mem
    (A : Finset (Fin 24)) (hA : A ∈ m24Blocks)
    (C : Finset (Fin 24)) (hC : C ∈ m24Blocks)
    (hInter : (A ∩ C).card = 4) :
    A ∆ C ∈ m24Blocks := by
  have hACard : A.card = 8 := m24Blocks_card A hA
  have hCCard : C.card = 8 := m24Blocks_card C hC
  have hDisjoint : Disjoint (A \ C) (C \ A) := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxC
    simp only [Finset.mem_sdiff] at hxA hxC
    exact hxA.2 hxC.1
  have hSymmCard : (A ∆ C).card = 8 := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hDisjoint,
      Finset.card_sdiff, Finset.card_sdiff, hACard, hCCard]
    rw [Finset.inter_comm C A]
    omega
  rw [m24Blocks] at hA hC
  rcases Finset.mem_image.mp hA with ⟨i, -, hi⟩
  rcases Finset.mem_image.mp hC with ⟨j, -, hj⟩
  have hWordCard :
      (m24GolayWord
        (m24GolayMessageXor (m24BlockMessage i) (m24BlockMessage j))).card = 8 := by
    rw [m24GolayWord_symmDiff, ← m24BlockAt_eq_m24GolayWord,
      ← m24BlockAt_eq_m24GolayWord, hi, hj]
    exact hSymmCard
  have hWordMem := m24GolayWord_mem_blocks_of_card_eq_eight _ hWordCard
  rw [m24GolayWord_symmDiff, ← m24BlockAt_eq_m24GolayWord,
    ← m24BlockAt_eq_m24GolayWord, hi, hj] at hWordMem
  exact hWordMem

private theorem m23SymmDiffBlock_mem_m24Blocks
    (B : Finset (Fin 23)) (hB : B ∈ m23Blocks)
    (C : Finset (Fin 23)) (hC : C ∈ m23Blocks)
    (hInter : (B ∩ C).card = 3) :
    m23SymmDiffBlock (B, C) ∈ m24Blocks := by
  have hAugB := m23AugmentedBlock_mem_m24Blocks B hB
  have hAugC := m23AugmentedBlock_mem_m24Blocks C hC
  have hAugInter :
      (m23AugmentedBlock B ∩ m23AugmentedBlock C).card = 4 := by
    rw [m23AugmentedBlock_inter, m23AugmentedBlock_card, hInter]
  have hMem := m24Blocks_symmDiff_mem
    (m23AugmentedBlock B) hAugB (m23AugmentedBlock C) hAugC hAugInter
  change m23LiftBlock B ∆ m23LiftBlock C ∈ m24Blocks
  rw [← m23AugmentedBlock_symmDiff]
  exact hMem

private theorem m24Block_mem_m23ReconstructedBlocks
    (C : Finset (Fin 24)) (hC : C ∈ m24Blocks) :
    C ∈ m23ReconstructedBlocks := by
  rw [m23ReconstructedBlocks, Finset.mem_union]
  by_cases h24 : (24 : Fin 24) ∈ C
  · left
    have hFiltered :
        C ∈ m24Blocks.filter (fun B => (24 : Fin 24) ∈ B) :=
      Finset.mem_filter.mpr ⟨hC, h24⟩
    rw [m24Blocks_through_24] at hFiltered
    exact hFiltered
  · right
    obtain ⟨S, hSC, hSCard⟩ :=
      Finset.exists_subset_card_eq
        (show 4 ≤ C.card by
          rw [m24Blocks_card C hC]
          omega)
    have h24S : (24 : Fin 24) ∉ S := fun h =>
      h24 (hSC h)
    have hInsertCard : (insert (24 : Fin 24) S).card = 5 := by
      rw [Finset.card_insert_of_notMem h24S, hSCard]
    have hUnique := m24Blocks_unique_block
      (insert (24 : Fin 24) S) hInsertCard
    obtain ⟨A, hAsingle⟩ := Finset.card_eq_one.mp hUnique
    have hAFiltered :
        A ∈ m24Blocks.filter
          (fun B => insert (24 : Fin 24) S ⊆ B) := by
      rw [hAsingle]
      simp
    have hAData := Finset.mem_filter.mp hAFiltered
    have hA24 : (24 : Fin 24) ∈ A :=
      hAData.2 (Finset.mem_insert_self _ _)
    have hAneC : A ≠ C := by
      intro hAC
      rw [hAC] at hA24
      exact h24 hA24
    have hSInter : S ⊆ A ∩ C := by
      apply Finset.subset_inter
      · intro x hx
        exact hAData.2 (Finset.mem_insert_of_mem hx)
      · exact hSC
    have hInterLe : 4 ≤ (A ∩ C).card := by
      rw [← hSCard]
      exact Finset.card_le_card hSInter
    have hInterLt : (A ∩ C).card < 5 := by
      have hAIndex := hAData.1
      have hCIndex := hC
      rw [m24Blocks] at hAIndex hCIndex
      rcases Finset.mem_image.mp hAIndex with ⟨i, -, hi⟩
      rcases Finset.mem_image.mp hCIndex with ⟨j, -, hj⟩
      rw [← hi, ← hj]
      apply m24BlockAt_inter i j
      intro hij
      apply hAneC
      rw [← hi, ← hj, hij]
    have hInter : (A ∩ C).card = 4 := by omega
    let D := A ∆ C
    have hD : D ∈ m24Blocks :=
      m24Blocks_symmDiff_mem A hAData.1 C hC hInter
    have hD24 : (24 : Fin 24) ∈ D := by
      change (24 : Fin 24) ∈ A ∆ C
      exact Finset.mem_symmDiff.mpr (Or.inl ⟨hA24, h24⟩)
    have hAThrough :
        A ∈ m24Blocks.filter (fun B => (24 : Fin 24) ∈ B) :=
      Finset.mem_filter.mpr ⟨hAData.1, hA24⟩
    have hDThrough :
        D ∈ m24Blocks.filter (fun B => (24 : Fin 24) ∈ B) :=
      Finset.mem_filter.mpr ⟨hD, hD24⟩
    rw [m24Blocks_through_24] at hAThrough hDThrough
    rcases Finset.mem_image.mp hAThrough with ⟨B, hB, hBA⟩
    rcases Finset.mem_image.mp hDThrough with ⟨E, hE, hED⟩
    have hADiff : A ∩ D = A \ C := by
      ext x
      by_cases hxA : x ∈ A <;> by_cases hxC : x ∈ C <;>
        simp [D, Finset.mem_symmDiff, hxA, hxC]
    have hADInter : (A ∩ D).card = 4 := by
      rw [hADiff, Finset.card_sdiff, m24Blocks_card A hAData.1,
        Finset.inter_comm C A, hInter]
    have hAugInter :
        (m23AugmentedBlock B ∩ m23AugmentedBlock E).card = 4 := by
      rw [hBA, hED]
      exact hADInter
    have hBEInter : (B ∩ E).card = 3 := by
      rw [m23AugmentedBlock_inter, m23AugmentedBlock_card] at hAugInter
      omega
    have hRecover : A ∆ D = C := by
      ext x
      by_cases hxA : x ∈ A <;> by_cases hxC : x ∈ C <;>
        simp [D, hxC]
    apply Finset.mem_image.mpr
    refine ⟨(B, E), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hB, hE⟩, hBEInter⟩
    · change m23LiftBlock B ∆ m23LiftBlock E = C
      rw [← m23AugmentedBlock_symmDiff, hBA, hED, hRecover]

private theorem m24Blocks_eq_m23Reconstruction :
    m24Blocks = m23ReconstructedBlocks := by
  ext C
  constructor
  · exact m24Block_mem_m23ReconstructedBlocks C
  · intro hC
    rw [m23ReconstructedBlocks, Finset.mem_union] at hC
    rcases hC with hAug | hSymm
    · rcases Finset.mem_image.mp hAug with ⟨B, hB, rfl⟩
      exact m23AugmentedBlock_mem_m24Blocks B hB
    · rcases Finset.mem_image.mp hSymm with ⟨p, hp, rfl⟩
      have hpData := Finset.mem_filter.mp hp
      have hpBlocks := Finset.mem_product.mp hpData.1
      exact m23SymmDiffBlock_mem_m24Blocks
        p.1 hpBlocks.1 p.2 hpBlocks.2 hpData.2
private theorem m23_smul_blocks (g : M23) :
    (g : Equiv.Perm (Fin 23)) • m23Blocks = m23Blocks := by
  have hg := (mem_M23_iff (g : Equiv.Perm (Fin 23))).mp g.property
  apply Finset.coe_injective
  simpa only [Finset.coe_smul_finset] using hg

private theorem m23ExtendHom_smul_liftBlock (g : M23) (B : Finset (Fin 23)) :
    m23ExtendHom g • m23LiftBlock B =
      m23LiftBlock ((g : Equiv.Perm (Fin 23)) • B) := by
  ext x
  simp [m23LiftBlock, Finset.mem_smul_finset, m23ExtendHom_apply_embedded]

private theorem m23ExtendHom_smul_augmentedBlock (g : M23) (B : Finset (Fin 23)) :
    m23ExtendHom g • m23AugmentedBlock B =
      m23AugmentedBlock ((g : Equiv.Perm (Fin 23)) • B) := by
  rw [m23AugmentedBlock, m23AugmentedBlock, Finset.smul_finset_insert]
  change
    insert (m23ExtendHom g (24 : Fin 24))
        (m23ExtendHom g • m23LiftBlock B) =
      insert (24 : Fin 24)
        (m23LiftBlock ((g : Equiv.Perm (Fin 23)) • B))
  rw [m23ExtendHom_apply_24, m23ExtendHom_smul_liftBlock]

private theorem m23ExtendHom_smul_symmDiffBlock
    (g : M23) (p : Finset (Fin 23) × Finset (Fin 23)) :
    m23ExtendHom g • m23SymmDiffBlock p =
      m23SymmDiffBlock
        ((g : Equiv.Perm (Fin 23)) • p.1, (g : Equiv.Perm (Fin 23)) • p.2) := by
  simp [m23SymmDiffBlock, Finset.smul_finset_symmDiff,
    m23ExtendHom_smul_liftBlock]

private theorem m23ExtendHom_smul_reconstructedBlocks (g : M23) :
    m23ExtendHom g • m23ReconstructedBlocks = m23ReconstructedBlocks := by
  apply Finset.eq_of_subset_of_card_le
  · intro C hC
    rcases Finset.mem_smul_finset.mp hC with ⟨D, hD, rfl⟩
    rw [m23ReconstructedBlocks, Finset.mem_union] at hD ⊢
    rcases hD with hAug | hSymm
    · rcases Finset.mem_image.mp hAug with ⟨B, hB, rfl⟩
      left
      rw [m23ExtendHom_smul_augmentedBlock]
      apply Finset.mem_image.mpr
      refine ⟨(g : Equiv.Perm (Fin 23)) • B, ?_, rfl⟩
      rw [← m23_smul_blocks g]
      exact Finset.smul_mem_smul_finset hB
    · rcases Finset.mem_image.mp hSymm with ⟨p, hp, rfl⟩
      right
      rw [m23ExtendHom_smul_symmDiffBlock]
      apply Finset.mem_image.mpr
      refine ⟨((g : Equiv.Perm (Fin 23)) • p.1,
        (g : Equiv.Perm (Fin 23)) • p.2), ?_, rfl⟩
      rw [Finset.mem_filter] at hp ⊢
      rcases hp with ⟨hpBlocks, hpInter⟩
      have hpBlocks' := Finset.mem_product.mp hpBlocks
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · rw [← m23_smul_blocks g]
          exact Finset.smul_mem_smul_finset hpBlocks'.1
        · rw [← m23_smul_blocks g]
          exact Finset.smul_mem_smul_finset hpBlocks'.2
      · rw [← Finset.smul_finset_inter, Finset.card_smul_finset]
        exact hpInter
  · simp
/-- Extending a W23 automorphism by fixing Atlas point 24 gives a W24 automorphism. -/
public theorem m23Extend_mem_M24 (g : M23) : m23ExtendHom g ∈ M24 := by
  rw [mem_M24_iff]
  have hFinset : m23ExtendHom g • m24Blocks = m24Blocks := by
    rw [m24Blocks_eq_m23Reconstruction]
    exact m23ExtendHom_smul_reconstructedBlocks g
  have hSet := congrArg
    (fun s : Finset (Finset (Fin 24)) => (s : Set (Finset (Fin 24)))) hFinset
  simpa only [Finset.coe_smul_finset] using hSet
/-- The extension homomorphism, valued in the M24 stabilizer of Atlas point 24. -/
public noncomputable def m23ToM24PointStabilizer :
    M23 →* MulAction.stabilizer M24 (24 : Fin 24) :=
  (m23ExtendHom.codRestrict M24 (fun g => m23Extend_mem_M24 g)).codRestrict
    (MulAction.stabilizer M24 (24 : Fin 24)) (fun g => by
      rw [MulAction.mem_stabilizer_iff]
      exact m23ExtendHom_apply_24 g)

/-- The extension into the M24 point stabilizer is injective. -/
public theorem m23ToM24PointStabilizer_injective :
    Function.Injective m23ToM24PointStabilizer := by
  intro g h hgh
  apply m23ExtendHom_injective
  have hPerm := congrArg
    (fun k : MulAction.stabilizer M24 (24 : Fin 24) =>
      ((k : M24) : Equiv.Perm (Fin 24))) hgh
  change m23ExtendHom g = m23ExtendHom h at hPerm
  exact hPerm
private theorem m24PointStabilizer_ne_24_iff
    (g : MulAction.stabilizer M24 (24 : Fin 24)) (x : Fin 24) :
    ((g : M24) : Equiv.Perm (Fin 24)) x ≠ (24 : Fin 24) ↔
      x ≠ (24 : Fin 24) := by
  have hFix : ((g : M24) : Equiv.Perm (Fin 24)) (24 : Fin 24) =
      (24 : Fin 24) := g.property
  simpa only [hFix] using
    not_congr
      (((g : M24) : Equiv.Perm (Fin 24)).injective.eq_iff :
        ((g : M24) : Equiv.Perm (Fin 24)) x =
            ((g : M24) : Equiv.Perm (Fin 24)) (24 : Fin 24) ↔
          x = (24 : Fin 24))

private noncomputable def m24PointStabilizerComplementHom :
    MulAction.stabilizer M24 (24 : Fin 24) →*
      Equiv.Perm {x : Fin 24 // x ≠ (24 : Fin 24)} where
  toFun g :=
    ((g : M24) : Equiv.Perm (Fin 24)).subtypePerm
      (m24PointStabilizer_ne_24_iff g)
  map_one' := by
    ext x
    rfl
  map_mul' g h := by
    ext x
    rfl

private noncomputable def m24PointStabilizerRestrictHom :
    MulAction.stabilizer M24 (24 : Fin 24) →* Equiv.Perm (Fin 23) :=
  m23PointEquiv.symm.permCongrHom.toMonoidHom.comp
    m24PointStabilizerComplementHom

set_option maxRecDepth 100000 in
private theorem m24PointStabilizerRestrictHom_apply
    (g : MulAction.stabilizer M24 (24 : Fin 24)) (i : Fin 23) :
    m23PointEmbedding (m24PointStabilizerRestrictHom g i) =
      ((g : M24) : Equiv.Perm (Fin 24)) (m23PointEmbedding i) := by
  change
    (m23PointEquiv
      (m23PointEquiv.symm.permCongr
        (m24PointStabilizerComplementHom g) i)).1 =
      ((g : M24) : Equiv.Perm (Fin 24)) (m23PointEquiv i).1
  rw [Equiv.permCongr_apply, m23PointEquiv.apply_symm_apply]
  rfl
private theorem m24PointStabilizer_smul_blocks
    (g : MulAction.stabilizer M24 (24 : Fin 24)) :
    ((g : M24) : Equiv.Perm (Fin 24)) • m24Blocks = m24Blocks := by
  have hg := (mem_M24_iff ((g : M24) : Equiv.Perm (Fin 24))).mp
    (g : M24).property
  apply Finset.coe_injective
  simpa only [Finset.coe_smul_finset] using hg

private theorem m24PointStabilizer_smul_liftBlock
    (g : MulAction.stabilizer M24 (24 : Fin 24)) (B : Finset (Fin 23)) :
    ((g : M24) : Equiv.Perm (Fin 24)) • m23LiftBlock B =
      m23LiftBlock (m24PointStabilizerRestrictHom g • B) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_smul_finset.mp hx with ⟨y, hy, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨a, ha, rfl⟩
    rw [m23LiftBlock, Finset.mem_map]
    exact ⟨m24PointStabilizerRestrictHom g a,
      Finset.smul_mem_smul_finset ha,
      m24PointStabilizerRestrictHom_apply g a⟩
  · intro hx
    rw [m23LiftBlock] at hx
    rcases Finset.mem_map.mp hx with ⟨a, ha, hax⟩
    rcases Finset.mem_smul_finset.mp ha with ⟨b, hb, rfl⟩
    apply Finset.mem_smul_finset.mpr
    refine ⟨m23PointEmbedding b, Finset.mem_map.mpr ⟨b, hb, rfl⟩, ?_⟩
    change ((g : M24) : Equiv.Perm (Fin 24)) (m23PointEmbedding b) = x
    rw [← m24PointStabilizerRestrictHom_apply g b]
    exact hax

private theorem m24PointStabilizer_smul_augmentedBlock
    (g : MulAction.stabilizer M24 (24 : Fin 24)) (B : Finset (Fin 23)) :
    ((g : M24) : Equiv.Perm (Fin 24)) • m23AugmentedBlock B =
      m23AugmentedBlock (m24PointStabilizerRestrictHom g • B) := by
  rw [m23AugmentedBlock, m23AugmentedBlock, Finset.smul_finset_insert]
  change
    insert (((g : M24) : Equiv.Perm (Fin 24)) (24 : Fin 24))
        (((g : M24) : Equiv.Perm (Fin 24)) • m23LiftBlock B) =
      insert (24 : Fin 24)
        (m23LiftBlock (m24PointStabilizerRestrictHom g • B))
  rw [show ((g : M24) : Equiv.Perm (Fin 24)) (24 : Fin 24) =
    (24 : Fin 24) from g.property, m24PointStabilizer_smul_liftBlock]

private theorem m24PointStabilizer_smul_m23Blocks
    (g : MulAction.stabilizer M24 (24 : Fin 24)) :
    m24PointStabilizerRestrictHom g • m23Blocks = m23Blocks := by
  apply Finset.eq_of_subset_of_card_le
  · intro C hC
    rcases Finset.mem_smul_finset.mp hC with ⟨B, hB, rfl⟩
    have hAugmented : m23AugmentedBlock B ∈ m24Blocks := by
      have hImage : m23AugmentedBlock B ∈
          m23Blocks.image m23AugmentedBlock :=
        Finset.mem_image.mpr ⟨B, hB, rfl⟩
      rw [← m24Blocks_through_24] at hImage
      exact (Finset.mem_filter.mp hImage).1
    have hMoved :
        ((g : M24) : Equiv.Perm (Fin 24)) • m23AugmentedBlock B ∈
          m24Blocks := by
      rw [← m24PointStabilizer_smul_blocks g]
      exact Finset.smul_mem_smul_finset hAugmented
    have hMoved24 : (24 : Fin 24) ∈
        ((g : M24) : Equiv.Perm (Fin 24)) • m23AugmentedBlock B := by
      rw [m24PointStabilizer_smul_augmentedBlock]
      exact Finset.mem_insert_self _ _
    have hFiltered :
        ((g : M24) : Equiv.Perm (Fin 24)) • m23AugmentedBlock B ∈
          m24Blocks.filter (fun D => (24 : Fin 24) ∈ D) :=
      Finset.mem_filter.mpr ⟨hMoved, hMoved24⟩
    rw [m24Blocks_through_24] at hFiltered
    rcases Finset.mem_image.mp hFiltered with ⟨B', hB', hB'⟩
    have hEq : B' = m24PointStabilizerRestrictHom g • B := by
      apply m23AugmentedBlock_injective
      rw [hB', m24PointStabilizer_smul_augmentedBlock]
    rwa [← hEq]
  · simp

private theorem m24PointStabilizerRestrictHom_mem_M23
    (g : MulAction.stabilizer M24 (24 : Fin 24)) :
    m24PointStabilizerRestrictHom g ∈ M23 := by
  rw [mem_M23_iff]
  have hFinset := m24PointStabilizer_smul_m23Blocks g
  have hSet := congrArg
    (fun s : Finset (Finset (Fin 23)) => (s : Set (Finset (Fin 23)))) hFinset
  simpa only [Finset.coe_smul_finset] using hSet
/-- Restrict an M24 automorphism fixing Atlas point 24 to the derived W23 design. -/
public noncomputable def m24PointStabilizerToM23 :
    MulAction.stabilizer M24 (24 : Fin 24) →* M23 :=
  m24PointStabilizerRestrictHom.codRestrict M23
    (fun g => m24PointStabilizerRestrictHom_mem_M23 g)

private theorem m24PointStabilizerToM23_m23ToM24PointStabilizer (g : M23) :
    m24PointStabilizerToM23 (m23ToM24PointStabilizer g) = g := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply m23PointEmbedding.injective
  change m23PointEmbedding
      (m24PointStabilizerRestrictHom (m23ToM24PointStabilizer g) i) =
    m23PointEmbedding ((g : Equiv.Perm (Fin 23)) i)
  rw [m24PointStabilizerRestrictHom_apply]
  change m23ExtendHom g (m23PointEmbedding i) =
    m23PointEmbedding ((g : Equiv.Perm (Fin 23)) i)
  exact m23ExtendHom_apply_embedded g i

private theorem m23ToM24PointStabilizer_m24PointStabilizerToM23
    (g : MulAction.stabilizer M24 (24 : Fin 24)) :
    m23ToM24PointStabilizer (m24PointStabilizerToM23 g) = g := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  by_cases hx : x = (24 : Fin 24)
  · subst x
    change m23ExtendHom (m24PointStabilizerToM23 g) (24 : Fin 24) =
      ((g : M24) : Equiv.Perm (Fin 24)) (24 : Fin 24)
    rw [m23ExtendHom_apply_24]
    exact g.property.symm
  · obtain ⟨i, hi⟩ := m23PointEquiv.surjective ⟨x, hx⟩
    have hEmbedding : m23PointEmbedding i = x := by
      change (m23PointEquiv i).1 = x
      exact congrArg Subtype.val hi
    rw [← hEmbedding]
    change m23ExtendHom (m24PointStabilizerToM23 g) (m23PointEmbedding i) =
      ((g : M24) : Equiv.Perm (Fin 24)) (m23PointEmbedding i)
    rw [m23ExtendHom_apply_embedded]
    exact m24PointStabilizerRestrictHom_apply g i

/-- The W23 automorphism group is the stabilizer of Atlas point 24 in M24. -/
public noncomputable def m23EquivM24PointStabilizer :
    M23 ≃* MulAction.stabilizer M24 (24 : Fin 24) where
  toFun := m23ToM24PointStabilizer
  invFun := m24PointStabilizerToM23
  left_inv := m24PointStabilizerToM23_m23ToM24PointStabilizer
  right_inv := m23ToM24PointStabilizer_m24PointStabilizerToM23
  map_mul' := m23ToM24PointStabilizer.map_mul

end Sporadic.Mathieu
