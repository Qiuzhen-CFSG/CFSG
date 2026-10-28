module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The octonion root and block coordinates are from the licensed ATLAS port,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see LICENSES/ATLAS-CITATION.cff. This extension computes the embedded affine
block, its two-core and its perfectness.
-/

public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LocalNormalizer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.IsPerfect

/-!
# The embedded affine block in the short-root centralizer

The A and B root groups together with the opposite-vector SL₂ stabilizer
form a concrete subgroup of the split-octonion G₂ model. Restricting the
long-parabolic projection gives a surjection onto SL₂ with kernel exactly
the A–B plane. In characteristic two this plane is the intrinsic two-core.
For fields larger than F₂ the block is perfect: the SL₂ image is perfect,
and the E–B commutator and long Weyl conjugation generate both translations.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp.1202–1203, case (a). This computes the
candidate residual without assuming that it is the whole centralizer residual.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups Pointwise commutatorElement
namespace Atlas.G2.ShortRootProducts.CentralizerCore
open LieParabolicSetup PairStabilizer
variable {F : Type*} [Field F] [CharP F 2]

def residualBlock : Subgroup (Model F) := longRootLocal ⊔ blockHom.range

theorem residualBlock_le_local : residualBlock (F := F) ≤ local₂ :=
  sup_le (longRootLocal_le_unipotent.trans unipotent_le_local₂)
    (by rintro _ ⟨M, rfl⟩; exact block_mem_local₂ M)

theorem block_le_longRootNormalizer :
    (blockHom (F := F)).range ≤ normalizer (longRootLocal (F := F) : Set (Model F)) := by
  rintro _ ⟨M, rfl⟩
  apply pointStabilizer_le_longRootNormalizer
  rw [← parabolic_eq_pointStabilizer]
  exact local₂_le_parabolic₂ (block_mem_local₂ M)

theorem residualBlock_factor {g : Model F} (hg : g ∈ residualBlock) :
    ∃ (p : Multiplicative (F × F)) (M : SL(2,F)), g = longRootHom p * blockHom M := by
  have hs := coe_mul_of_right_le_normalizer_left longRootLocal
    (blockHom (F := F)).range block_le_longRootNormalizer
  rw [← SetLike.mem_coe, residualBlock, hs] at hg
  obtain ⟨_, ⟨p, rfl⟩, _, ⟨M, rfl⟩, he⟩ := hg
  exact ⟨p, M, he.symm⟩

def blockProjection : residualBlock (F := F) →* SL(2,F) :=
  longSLHom.comp (inclusion residualBlock_le_local)

omit [CharP F 2] in
private theorem longRoot_le_radical : longRootLocal (F := F) ≤ radical₂ := by
  rintro _ ⟨p, rfl⟩
  exact ⟨![p.toAdd.1, p.toAdd.2, 0, 0, 0, 0], rfl, by simp [unipotentProduct, longRootHom]⟩

theorem blockProjection_longRoot (p : Multiplicative (F × F)) :
    blockProjection ⟨longRootHom p, mem_sup_left ⟨p, rfl⟩⟩ = 1 := by
  apply MonoidHom.mem_ker.mp
  change (⟨longRootHom p, _⟩ : local₂) ∈ longSLHom.ker
  rw [longSLHom_ker]
  exact longRoot_le_radical ⟨p,rfl⟩

theorem blockProjection_block (M : SL(2,F)) :
    blockProjection ⟨blockHom M, mem_sup_right ⟨M, rfl⟩⟩ = M :=
  longSLHom_section M

theorem blockProjection_surjective : Function.Surjective (blockProjection (F := F)) :=
  fun M => ⟨⟨blockHom M, mem_sup_right ⟨M,rfl⟩⟩, blockProjection_block M⟩

theorem blockProjection_ker : (blockProjection (F := F)).ker =
    longRootLocal.subgroupOf residualBlock := by
  ext g
  change blockProjection g = 1 ↔ g.val ∈ longRootLocal
  obtain ⟨p,M,he⟩ := residualBlock_factor g.property
  have hg : g = (⟨longRootHom p, mem_sup_left ⟨p,rfl⟩⟩ : residualBlock) *
      ⟨blockHom M, mem_sup_right ⟨M,rfl⟩⟩ := Subtype.ext he
  rw [hg, map_mul, blockProjection_longRoot, blockProjection_block, one_mul]
  constructor
  · intro hM
    change longRootHom p * blockHom M ∈ longRootLocal
    rw [hM, map_one, mul_one]
    exact ⟨p,rfl⟩
  · intro h
    have hk : (⟨g.val, residualBlock_le_local g.property⟩ : local₂) ∈ longSLHom.ker := by
      rw [longSLHom_ker]
      apply longRoot_le_radical
      change g.val ∈ longRootLocal
      rw [he]
      exact h
    have hx := MonoidHom.mem_ker.mp hk
    change blockProjection g = 1 at hx
    simpa only [hg, map_mul, blockProjection_longRoot, blockProjection_block, one_mul] using hx

theorem residualBlock_pCoreIn [Finite F] : (residualBlock (F := F)).pCoreIn 2 = longRootLocal := by
  have hk : pCore 2 (residualBlock (F := F)) = blockProjection.ker := by
    apply le_antisymm
    · have hn : ((pCore 2 (residualBlock (F := F))).map blockProjection).Normal :=
        Subgroup.Normal.map inferInstance blockProjection blockProjection_surjective
      have hp : IsPGroup 2 ((pCore 2 (residualBlock (F := F))).map blockProjection) :=
        pCore_isPGroup.map blockProjection
      have hle : (pCore 2 (residualBlock (F := F))).map blockProjection ≤ pCore 2 SL(2,F) :=
        le_sSup ⟨hn,hp⟩
      rw [Matrix.SL2.twoCore_eq_bot] at hle
      exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hle)
    · apply le_sSup
      refine ⟨inferInstance, ?_⟩
      rw [blockProjection_ker]
      exact ((unipotent_isTwoGroup (F := F)).of_injective
        (inclusion longRootLocal_le_unipotent) (inclusion_injective _)).comap_subtype
  rw [pCoreIn, hk, blockProjection_ker]
  exact map_subgroupOf_eq_of_le (show longRootLocal ≤ residualBlock (F := F) from le_sup_left)

theorem residualBlock_isPerfect [Finite F] (hq : 2 < Nat.card F) :
    Group.IsPerfect (residualBlock (F := F)) := by
  classical
  let := Fintype.ofFinite F
  have hc : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have ht' : t ≠ 0 ∧ t ≠ 1 := by simpa using ht
  have ht2 : t ^ 2 ≠ 1 := by
    intro he
    rcases sq_eq_one_iff.mp he with he | he
    · exact ht'.2 he
    · exact ht'.2 (by simpa only [CharTwo.neg_eq] using he)
  let : Group.IsPerfect SL(2,F) := ⟨Matrix.SL2.commutator_eq_top ht'.1 ht2⟩
  let B := residualBlock (F := F)
  let H : Subgroup (Model F) := ⁅B,B⁆
  have hblock : blockHom.range ≤ H := by
    let : Group.IsPerfect (blockHom (F := F)).range := Group.IsPerfect.range blockHom
    rw [← Subgroup.commutator_eq_self (H := blockHom.range)]
    exact commutator_mono le_sup_right le_sup_right
  have hE : rootE (1 : F) ∈ B := by
    rw [← block_upper]
    exact mem_sup_right ⟨_,rfl⟩
  have hA (a : F) : rootA a ∈ H := by
    have he : ⁅rootE (1 : F), rootB a⁆ = rootA a := by
      rw [commutatorElement_def]
      change MulAut.conj (rootE (1 : F)) (rootB a) * (rootB a)⁻¹ = _
      rw [rootE_conjugate_rootB, one_mul, mul_inv_cancel_right]
    rw [← he]
    exact commutator_mem_commutator hE (mem_sup_left (rootB_mem_longRootLocal a))
  have hR : (weylR : Model F) ∈ B := by
    rw [← long_block_J]
    exact mem_sup_right ⟨_,rfl⟩
  have hB (a : F) : rootB a ∈ H := by
    rw [← weylR_rootA]
    exact (mem_normalizer_iff.mp (normalizer_commutator_ge_left B B hR) _).mp (hA a)
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (commutator_le_self _) (sup_le ?_ hblock)
  rintro _ ⟨p,rfl⟩
  exact H.mul_mem (hA p.toAdd.1) (hB p.toAdd.2)

theorem residualBlock_isTwoPerfect [Finite F] (hq : 2 < Nat.card F) :
    IsPPerfect 2 (residualBlock (F := F)) := by
  let := residualBlock_isPerfect (F := F) hq
  intro N hN hp
  let := hN
  have : Subsingleton (residualBlock (F := F) ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

end Atlas.G2.ShortRootProducts.CentralizerCore
