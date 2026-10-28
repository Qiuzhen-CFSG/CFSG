module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.MovingBlock

/-!
# The literal block quotient and its rank-one field degree

When [W_K,K] is the embedded U(K), its map to the moving section is
surjective with kernel exactly C_U(K). The first isomorphism theorem gives
an equivalence from the actual BlockModule K to the actual section. The
conjugation equation retains the original componentMap on representatives.

Thus any natural section for SL₂(F), with |F|=2ⁿ, fixes the exponent of an
L₂-even block alternative. The source application uses a block relative to
KTᵥ and the proved source_moving_eq_blockU identity. Construction of the
natural section and exclusion of the A₅ permutation action remain separate.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, C.1.7–12,
pp.123–124, and 13.6.18, p.931 (PDF p.948).
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open ComponentSelection ComponentElimination.SourceTransferFields.RankOneBorel
open CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]
local notation "W" => WK K L T z v
local notation "ρ" => componentRepresentation K L T z v hL hz
local notation "D" => movingSpace K L T z v
local notation "C" => Submodule.comap (Submodule.subtype D) (Representation.invariants ρ)
include hL hz in
omit [IsElementaryAbelian 2 (WK K L T z v)] in
private theorem moving_le : ⁅W, K⁆ ≤ W :=
  le_normalizer_iff_commutator_le_left.mp
    ((K_le_plusActor K L T v).trans (plusActor_normalizes_WK K L T z v hL hz))
/-- The actual inclusion of U(K) in the moving subspace of W_K. -/
noncomputable def blockToMoving
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hm : ⁅W, K⁆ = (blockU K).map K.subtype) : blockU K →* Multiplicative D where
  toFun u := Multiplicative.ofAdd ⟨Additive.ofMul ⟨u.val.val,
    by exact moving_le K L T z v hL hz (hm.symm ▸ ⟨u.val, u.property, rfl⟩)⟩,
    by
      change u.val.val ∈ ⁅W, K⁆
      rw [hm]
      exact ⟨u.val, u.property, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem blockToMoving_surjective (hm : ⁅W, K⁆ = (blockU K).map K.subtype) : Function.Surjective
    (blockToMoving K L T z v hL hz hm) := by
  intro d
  have hd : d.toAdd.val.toMul.val ∈ (blockU K).map K.subtype := hm ▸ d.toAdd.property
  obtain ⟨u, hu, he⟩ := hd
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg Additive.ofMul (Subtype.ext he)

/-- The canonical map from U(K) to the moving section. -/
noncomputable def blockToSection (hm : ⁅W, K⁆ = (blockU K).map K.subtype) :
    blockU K →* Multiplicative (D ⧸ C) :=
  ((C).mkQ.toAddMonoidHom.toMultiplicative).comp (blockToMoving K L T z v hL hz hm)

theorem blockToSection_surjective (hm : ⁅W, K⁆ = (blockU K).map K.subtype) : Function.Surjective
    (blockToSection K L T z v hL hz hm) := by
  intro q
  obtain ⟨d, hd⟩ := Submodule.mkQ_surjective C q.toAdd
  obtain ⟨u, hu⟩ := blockToMoving_surjective K L T z v hL hz hm (Multiplicative.ofAdd d)
  exact ⟨u, congrArg ((C).mkQ.toAddMonoidHom.toMultiplicative) hu |>.trans
    (congrArg Multiplicative.ofAdd hd)⟩

/-- The quotient kills exactly U(K) ∩ Z(K). -/
theorem blockToSection_ker (hm : ⁅W, K⁆ = (blockU K).map K.subtype) :
    (blockToSection K L T z v hL hz hm).ker = blockFixed K := by
  ext u
  change Submodule.Quotient.mk (blockToMoving K L T z v hL hz hm u).toAdd =
    (0 : D ⧸ C) ↔ u.val ∈ center K
  rw [Submodule.Quotient.mk_eq_zero]
  change (blockToMoving K L T z v hL hz hm u).toAdd.val ∈ (ρ).invariants ↔ _
  refine (invariants_iff K L T z v hL hz
    (blockToMoving K L T z v hL hz hm u).toAdd.val.toMul).trans ?_
  constructor
  · intro h
    rw [mem_center_iff]
    intro k
    apply Subtype.ext
    exact mem_centralizer_iff.mp h k k.property
  · intro h k hk
    exact congrArg Subtype.val (mem_center_iff.mp h ⟨k, hk⟩)

/-- Identify both literal quotients via their canonical maps. -/
noncomputable def blockSectionEquiv (hm : ⁅W, K⁆ = (blockU K).map K.subtype) :
    BlockModule K ≃* Multiplicative (D ⧸ C) :=
  (QuotientGroup.quotientMulEquivOfEq (blockToSection_ker K L T z v hL hz hm).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (blockToSection K L T z v hL hz hm)
      (blockToSection_surjective K L T z v hL hz hm))

theorem blockSectionEquiv_mk (hm : ⁅W, K⁆ = (blockU K).map K.subtype) (u : blockU K) :
    blockSectionEquiv K L T z v hL hz hm (QuotientGroup.mk' (blockFixed K) u) =
      blockToSection K L T z v hL hz hm u := rfl

/-- The quotient equivalence intertwines conjugation with the literal plus action. -/
theorem blockSectionEquiv_conjugate (hm : ⁅W, K⁆ = (blockU K).map K.subtype)
    (k : K) (u : blockU K) :
    (blockSectionEquiv K L T z v hL hz hm
      (QuotientGroup.mk' (blockFixed K) (blockConjugate K k u))).toAdd =
    Replacement.Action.sectionRepresentation K L T z v hL hz
      (componentMap K L T z v hL hz k)
      (blockSectionEquiv K L T z v hL hz hm
        (QuotientGroup.mk' (blockFixed K) u)).toAdd := rfl

/-- The inclusion of the moving subgroup is injective. -/
theorem blockToMoving_injective (hm : ⁅W, K⁆ = (blockU K).map K.subtype) : Function.Injective
    (blockToMoving K L T z v hL hz hm) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun d : Multiplicative D => d.toAdd.val.toMul.val) h

/-- Coordinates before quotienting by the fixed vectors. -/
noncomputable def blockMovingEquiv (hm : ⁅W, K⁆ = (blockU K).map K.subtype) :
    blockU K ≃* Multiplicative D :=
  MulEquiv.ofBijective (blockToMoving K L T z v hL hz hm)
    ⟨blockToMoving_injective K L T z v hL hz hm,
      blockToMoving_surjective K L T z v hL hz hm⟩

open Matrix.SpecialLinearGroup.RankOneResidual
variable [Finite G]

omit [Finite G] in
/-- Cardinality of the actual block section from its natural coordinates. -/
theorem blockModule_card_of_natural (hm : ⁅W, K⁆ = (blockU K).map K.subtype)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (s : NaturalSection (F := F) ρ D) :
    Nat.card (BlockModule K) = 2 ^ (n * 2) := by
  have he := Nat.card_congr (blockSectionEquiv K L T z v hL hz hm).toEquiv
  change Nat.card (BlockModule K) = Nat.card (D ⧸ C) at he
  rw [he, Nat.card_congr s.coordinates.toEquiv, Nat.card_fun, Nat.card_fin, hF, pow_mul]

omit [Finite G] in
/-- Equality of the two module cardinalities recovers the identical exponent. -/
theorem l2EvenBlock_same_degree (hm : ⁅W, K⁆ = (blockU K).map K.subtype)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {m n : ℕ} (hF : Nat.card F = 2 ^ n)
    (s : NaturalSection (F := F) ρ D) (hb : IsL2EvenBlock K m) : m = n := by
  have he := hb.module_card.symm.trans (blockModule_card_of_natural K L T z v hL hz hm hF s)
  have he' := Nat.pow_right_injective (by decide : 1 < 2) he
  omega

/-- Apply the quotient comparison to the relative block inside KTᵥ. -/
noncomputable def sourceBlockSectionEquiv
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : IsBlock (K.subgroupOf (K ⊔ Tv T v))) :
    BlockModule K ≃* Multiplicative (D ⧸ C) :=
  blockSectionEquiv K L T z v hL hz
    (Replacement.MovingBlock.source_moving_eq_blockU K L T z v hL hz hK hn hW hb)

/-- A natural section for the actual moving space fixes the exponent of
any rank-one block alternative, at the same field degree n. -/
theorem source_l2EvenBlock_of_type {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] {m n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ Tv T v)
    (hb : IsBlock (K.subgroupOf (K ⊔ Tv T v)))
    (s : NaturalSection (F := F) ρ D) (htype : IsL2EvenBlock K m) :
    IsL2EvenBlock K n := by
  have hm := Replacement.MovingBlock.source_moving_eq_blockU K L T z v hL hz hK hn hW hb
  have he := l2EvenBlock_same_degree K L T z v hL hz hm hF s htype
  exact he ▸ htype
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
end
