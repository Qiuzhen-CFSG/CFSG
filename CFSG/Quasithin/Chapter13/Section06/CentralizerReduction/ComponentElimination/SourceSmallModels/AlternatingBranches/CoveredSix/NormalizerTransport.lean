module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Product
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.NaturalCoordinates
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Literal normalizers and the source commutator line

Subgroups of the ambient block layer are written as binary subspaces of U
without taking a quotient. Their stabilizer preimages are exactly their
ambient normalizers, and the full relative normalizers map onto the action
stabilizers. Characteristicity of O²(C_L(v)) proves normalization of Lᵥ
by Mᵥ; normalization of V then gives normalization of [V,Lᵥ].

The A₅ marking proves that this literal commutator has order four. Its
application below gives an invariant binary two-space once the marked-plane
normalizer is placed in Mᵥ. Construction of that plane and placement, and the
contrary hexacode stabilizer calculation, remain separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the local
notation and 13.6.5 on printed p.926, and 13.6.22 on printed p.932.
-/

@[expose] public section
open Subgroup CFSG.Quasithin.ChapterC Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
section Ambient
variable {G : Type*} [Group G] (K : Subgroup G)
variable (h : IsExceptionalAhat6Block K) [IsElementaryAbelian 2 (blockU K)]

/-- The binary subspace of the literal blockU coming from an ambient subgroup. -/
noncomputable def ambientSubspace (P : Subgroup G) :
    Submodule (ZMod 2) (Additive (blockU K)) :=
  NormalElementaryQuotient.subspace (blockU K) ((P.subgroupOf K).subgroupOf (blockU K))

omit [IsElementaryAbelian 2 (blockU K)] in
private theorem internal_le (P : Subgroup G) (hP : P ≤ (blockU K).map K.subtype) :
    P.subgroupOf K ≤ blockU K := by
  intro x hx
  obtain ⟨y, hy, he⟩ := hP hx
  exact (Subtype.ext he : y = x) ▸ hy

/-- These coordinates retain all elements of P; there is no further quotient. -/
noncomputable def ambientSubspaceEquiv (P : Subgroup G)
    (hP : P ≤ (blockU K).map K.subtype) : ambientSubspace K P ≃ P where
  toFun u := ⟨u.val.toMul.val.val, u.property⟩
  invFun p := ⟨Additive.ofMul ⟨⟨p, (hP.trans (map_subtype_le _)) p.property⟩,
    by
      obtain ⟨y, hy, he⟩ := hP p.property
      exact (Subtype.ext he : y = ⟨p, (hP.trans (map_subtype_le _)) p.property⟩) ▸ hy⟩,
    p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Stabilizing the coordinates is exactly normalizing the original subgroup. -/
theorem ambientSubspace_stabilizer (P : Subgroup G)
    (hP : P ≤ (blockU K).map K.subtype) (k : K) :
    QuotientGroup.mk' (pCore 2 K) k ∈
      BinaryOffender.subspaceStabilizer (binaryAction h) (ambientSubspace K P) ↔
        (k : G) ∈ normalizer (P : Set G) := by
  have he := NormalElementaryQuotient.stabilizer_comap (blockU K)
    (QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk', h.centralizer])
    ((P.subgroupOf K).subgroupOf (blockU K))
  rw [map_subgroupOf_eq_of_le (internal_le K P hP)] at he
  change k ∈ (BinaryOffender.subspaceStabilizer (binaryAction h)
    (ambientSubspace K P)).comap (QuotientGroup.mk' (pCore 2 K)) ↔ _
  unfold binaryAction ambientSubspace
  rw [he, ← subgroupOf_normalizer_eq (hP.trans (map_subtype_le _))]
  rfl

/-- The image uses the full relative normalizer, including every lift through O₂(K). -/
theorem ambientNormalizer_image (P : Subgroup G)
    (hP : P ≤ (blockU K).map K.subtype) :
    ((K ⊓ normalizer (P : Set G)).subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) =
      BinaryOffender.subspaceStabilizer (binaryAction h) (ambientSubspace K P) := by
  apply le_antisymm
  · rintro _ ⟨k, hk, rfl⟩
    exact (ambientSubspace_stabilizer K h P hP k).mpr hk.2
  · intro a ha
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) a
    exact ⟨k, ⟨k.property, (ambientSubspace_stabilizer K h P hP k).mp ha⟩, rfl⟩

/-- The order-four hypothesis is converted using the actual inclusion coordinates. -/
theorem ambientSubspace_finrank_two (P : Subgroup G)
    (hP : P ≤ (blockU K).map K.subtype) (hc : Nat.card P = 4) :
    Module.finrank (ZMod 2) (ambientSubspace K P) = 2 := by
  let : Finite P := Nat.finite_of_card_ne_zero (by omega)
  let : Finite (ambientSubspace K P) :=
    Finite.of_equiv P (ambientSubspaceEquiv K P hP).symm
  have he := Nat.card_congr (ambientSubspaceEquiv K P hP)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hc] at he
  exact Nat.pow_right_injective (by decide : 1 < 2) he
end Ambient

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
section SourceLine
variable {G : Type*} [Group G] {L M V : Subgroup G} {v : G}

/-- Residual characteristicity, relative to C_L(v), supplies normalization by M_v. -/
theorem Mv_normalizes_Lv (hML : M ≤ normalizer (L : Set G)) :
    Mv M v ≤ normalizer (Lv L v : Set G) := by
  have hn : Mv M v ≤ normalizer ((L ⊓ Gv v : Subgroup G) : Set G) :=
    (inf_le_inf hML (Gv v).le_normalizer).trans inf_normalizer_le_normalizer_inf
  exact hn.trans (normalizer_le_normalizer_characteristic_image (L ⊓ Gv v)
    (pResidual 2 ↥(L ⊓ Gv v)))

/-- Placement in M_v preserves both factors of the literal source commutator. -/
theorem source_commutator_normalized (N : Subgroup G)
    (hNM : N ≤ Mv M v) (hML : M ≤ normalizer (L : Set G))
    (hMV : Mv M v ≤ normalizer (V : Set G)) :
    N ≤ normalizer ((⁅V, Lv L v⁆ : Subgroup G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hMV (hNM hn)),
    mem_normalizer_iff_map_conj_eq.mp (Mv_normalizes_Lv hML (hNM hn))]

/-- The source A₅ marking makes l=[V,L_v] an actual group of order four. -/
theorem source_commutator_card [Finite G] (s : A5Module.Marking L V) :
    Nat.card (⁅V, Lv L (A5Module.markedV s)⁆ : Subgroup G) = 4 := by
  rw [A5Module.residual_commutator_eq_moved s,
    card_map_of_injective s.injective,
    Nat.card_congr A5Module.ResidualCoordinates.movedCoreEquiv.toEquiv]
  change Nat.card (BinaryPermutation.core (Fin 3)) = 4
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    BinaryPermutation.finrank_core]
  norm_num

end SourceLine

section SourceConsumer
variable {G : Type*} [Group G] [Finite G] {L M V : Subgroup G}
    (K : Subgroup G) (h : IsExceptionalAhat6Block K)
    [IsElementaryAbelian 2 (blockU K)]

/-- On the actual source line, placement of the plane normalizer supplies
both the binary dimension and invariance required by the model obstruction. -/
theorem source_line_invariant_of_placement (s : A5Module.Marking L V)
    (P : Subgroup G) (hP : P ≤ (blockU K).map K.subtype)
    (hl : ⁅V, Lv L (A5Module.markedV s)⁆ ≤ (blockU K).map K.subtype)
    (hNP : K ⊓ normalizer (P : Set G) ≤ Mv M (A5Module.markedV s))
    (hML : M ≤ normalizer (L : Set G))
    (hMV : Mv M (A5Module.markedV s) ≤ normalizer (V : Set G)) :
    Module.finrank (ZMod 2) (ambientSubspace K ⁅V, Lv L (A5Module.markedV s)⁆) = 2 ∧
      BinaryOffender.subspaceStabilizer (binaryAction h) (ambientSubspace K P) ≤
        BinaryOffender.subspaceStabilizer (binaryAction h)
          (ambientSubspace K ⁅V, Lv L (A5Module.markedV s)⁆) := by
  refine ⟨ambientSubspace_finrank_two K _ hl (source_commutator_card s), ?_⟩
  intro g hg
  rw [← ambientNormalizer_image K h P hP] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  exact (ambientSubspace_stabilizer K h _ hl k).mpr
    (source_commutator_normalized _ hNP hML hMV hk)
end SourceConsumer

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
