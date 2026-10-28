module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Defs
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.SolvableShortAbelianCore.QuotientThree
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic.AlternatingThree

/-!
# The actual cubic branch of block commutation

A short group with two-core quotient of order three has O₂(X)=U(X),
an elementary four-group. The existing conjugation-module construction
therefore identifies it as an actual alternating-three block. This
activates precisely the published guard of C.1.9, with no model tag or
extra representation hypothesis. Subnormality puts every such block
inside the preimage of O₃(G/O₂(G)).

The final commutation of two distinct cubic blocks remains a separate
obligation. These results supply its actual model, ambient placement,
and characteristic-two input.

Source: Aschbacher--Smith C.1.7--9 and C.1.12--13, printed pp.123--125
(combined manuscript of 1 March 2004). The core equality proof reuses the
argument of `SolvableShortAbelianCore`, retaining that module unchanged.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC

variable {L : Type*} [Group L]

/-- The core of a cubic short group is exactly its elementary commutator layer. -/
theorem IsShort.core_eq_blockU_of_quotient_three (h : IsShort L)
    (hq : Nat.card (L ⧸ pCore 2 L) = 3) : pCore 2 L = blockU L := by
  let := h.finite
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic (L ⧸ pCore 2 L) := isCyclic_of_prime_card hq
  let f := QuotientGroup.lift (blockU L) (QuotientGroup.mk' (pCore 2 L))
    (by simpa only [QuotientGroup.ker_mk'] using (blockU_le_core (L := L)))
  have hk : f.ker = (pCore 2 L).map (QuotientGroup.mk' (blockU L)) := by
    dsimp [f]
    rw [QuotientGroup.ker_lift, QuotientGroup.ker_mk']
  let : IsMulCommutative (L ⧸ blockU L) :=
    f.isMulCommutative_of_isCyclic_of_ker_le_center (hk ▸ blockU_core_image_le_center)
  have hc : Nat.Coprime 2 (Nat.card (L ⧸ blockU L)) := by
    have hh := coprime_card_pResidual_of_commGroup (A := L ⧸ blockU L) 2
    rwa [(pResidual_eq_top_iff 2 _).mpr (h.quotient_twoPerfect (blockU L)), card_top] at hh
  have hb : (pCore 2 L).map (QuotientGroup.mk' (blockU L)) = ⊥ := by
    apply (Subgroup.card_eq_one).mp
    rcases (pCore_isPGroup (p := 2) (G := L)).map (QuotientGroup.mk' (blockU L)) |>.card_eq_or_dvd with h1 | h2
    · exact h1
    · exact (Nat.prime_two.coprime_iff_not_dvd.mp hc
        (h2.trans (card_subgroup_dvd_card _))).elim
  exact le_antisymm (by simpa only [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hb)
    blockU_le_core

/-- The cubic short core has four elements, without an extra abelianness hypothesis. -/
theorem IsShort.core_card_four_of_quotient_three (h : IsShort L)
    (hq : Nat.card (L ⧸ pCore 2 L) = 3) : Nat.card (pCore 2 L) = 4 := by
  let := h.finite
  have he := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 L)
  rw [hq, h.card_eq_twelve_of_quotient_three hq] at he
  omega

/-- A cubic short group has the actual natural alternating-three conjugation module. -/
theorem IsShort.isAlternatingBlock_of_quotient_three (h : IsShort L)
    (hq : Nat.card (L ⧸ pCore 2 L) = 3) : IsAlternatingBlock L 3 := by
  let := h.finite
  have he : IsElementaryAbelian 2 (pCore 2 L) := by
    rw [h.core_eq_blockU_of_quotient_three hq]
    exact h.elementary
  exact RankOne.Solvable.MinimalParabolic.alternatingThree_of_elementary_four_core
    h.twoPerfect he (h.core_card_four_of_quotient_three hq) hq

variable {G : Type*} [Group G] [Finite G]

/-- The cubic image is a subnormal three-subgroup, so the original block lies in O₂,₃. -/
theorem IsBlock.le_upperTwoThreeCore_of_quotient_three {X : Subgroup G}
    (hX : IsBlock X) (hqX : Nat.card (X ⧸ pCore 2 X) = 3) : X ≤ upperTwoThreeCore G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hcard : Nat.card (X.map q) = 3 :=
    (Nat.card_congr (BlockCommutation.coreQuotientEquiv X hX.subnormal).toEquiv).symm.trans hqX
  have hp : IsPGroup 3 (X.map q) := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hs := hX.subnormal.map (QuotientGroup.mk'_surjective (pCore 2 G))
  have he : (X.map q).pCoreIn 3 = X.map q := by
    have ht : pCore 3 (X.map q) = ⊤ := top_unique
      (le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩)
    rw [pCoreIn, ht, ← MonoidHom.range_eq_map, range_subtype]
  have hle := pCoreIn_le_of_subnormal 3 hs
  rw [he] at hle
  exact map_le_iff_le_comap.mp hle

omit [Finite G] in
/-- An actual cubic block discharges the antecedent of the published C.1.9 guard. -/
theorem BlockCommutationHypothesis.fitting_of_quotient_three
    (hG : BlockCommutationHypothesis G) {X : Subgroup G}
    (hX : IsBlock X) (hqX : Nat.card (X ⧸ pCore 2 X) = 3) :
    generalizedFitting (upperTwoThreeCore G) = pCore 2 (upperTwoThreeCore G) :=
  hG ⟨X, hX, hX.short.isAlternatingBlock_of_quotient_three hqX⟩

/-- The ambient core's displacement by a block is exactly the block's own U-layer. -/
theorem IsBlock.ambient_core_commutator {X : Subgroup G} (hX : IsBlock X) :
    ⁅pCore 2 G, X⁆ = (blockU X).map X.subtype := by
  apply le_antisymm
  · exact commutator_le_core_commutator_of_isSubnormal X (pCore 2 G)
      hX.subnormal hX.short.twoPerfect pCore_isPGroup le_normalizer_of_normal
  · rw [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact commutator_mono (pCoreIn_le_of_subnormal 2 hX.subnormal) le_rfl

/-- The exact structural inputs now available for each block in the remaining cubic case. -/
theorem IsBlock.cubic_commutation_setup {X : Subgroup G} (hX : IsBlock X)
    (hqX : Nat.card (X ⧸ pCore 2 X) = 3) (hG : BlockCommutationHypothesis G) :
    IsAlternatingBlock X 3 ∧ X ≤ upperTwoThreeCore G ∧
      generalizedFitting (upperTwoThreeCore G) = pCore 2 (upperTwoThreeCore G) ∧
      Nat.card ((blockU X).map X.subtype) = 4 ∧
      ⁅pCore 2 G, X⁆ = (blockU X).map X.subtype ∧
      pCore 2 G ≤ centralizer ((blockU X).map X.subtype : Set G) := by
  refine ⟨hX.short.isAlternatingBlock_of_quotient_three hqX,
    hX.le_upperTwoThreeCore_of_quotient_three hqX,
    hG.fitting_of_quotient_three hX hqX, ?_,
    hX.ambient_core_commutator, hX.core_centralizes_blockU⟩
  rw [card_subtype, ← hX.short.core_eq_blockU_of_quotient_three hqX]
  exact hX.short.core_card_four_of_quotient_three hqX

end CFSG.Quasithin.ChapterC
