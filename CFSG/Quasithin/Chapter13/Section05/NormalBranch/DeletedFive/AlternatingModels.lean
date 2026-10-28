module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive.Cardinality
public import Theory.SpecificGroups.BinaryLinear.FourTwoLocalFive
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.Sylow
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Alternating and binary linear exclusions for the deleted-five branch

The literal alternating-five block has a quotient of order sixty and a
commutator layer of order sixteen, so its order is divisible by 960. This
excludes Aₙ for n ≤ 7. In GL₄(2), every nonidentity two-subgroup has a
normalizer of order prime to five, excluding the same block and hence A₈
through the proved exceptional isomorphism. Finally PSL₅(2) has Sylow
2-subgroups of order 1024, exceeding the source bound 256.

These are the alternating and binary linear rows of the Theorem C inspection
in Aschbacher–Smith 13.5.15, printed p.921. The original block and its
characteristic commutator layer are retained by each model equivalence.
-/

public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
open ChapterC
variable {G : Type*} [Group G] [Finite G]

private instance : Finite (BinaryLinear.OuterCyclic.LinearGroup 4) :=
  Finite.of_equiv (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))
    (BinaryLinear.OuterCyclic.matrixEquivLinear 4).toEquiv

omit [Finite G] in
private theorem five_dvd_block_card (K : Subgroup G) (hK : IsAlternatingBlock K 5) :
    5 ∣ Nat.card K := by
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K), alternatingFive_quotient_card K hK]
  exact dvd_mul_of_dvd_left (by decide) _

private theorem no_block_in_linear_four
    (K : Subgroup (BinaryLinear.OuterCyclic.LinearGroup 4))
    (hK : IsAlternatingBlock K 5)
    (hc : Nat.card ((blockU K).map K.subtype) = 16) : False := by
  let U := (blockU K).map K.subtype
  let := hK.2.1.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map K.subtype
  have hU0 : U ≠ ⊥ := by
    intro he
    change Nat.card U = 16 at hc
    rw [he, card_bot] at hc
    omega
  have hKU : K ≤ normalizer (U : Set (BinaryLinear.OuterCyclic.LinearGroup 4)) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  exact BinaryLinear.FourTwoLocalFive.five_not_dvd_normalizer U
    (IsElementaryAbelian.isPGroup 2 U) hU0
    ((five_dvd_block_card K hK).trans (card_dvd_of_le hKU))

/-- A source deleted-five block cannot occur in a binary degree-four linear group. -/
theorem not_psl4Two_of_alternatingFive
    (K : Subgroup G) (hK : IsAlternatingBlock K 5)
    (hc : Nat.card ((blockU K).map K.subtype) = 16)
    (hmodel : ClassicalGroup.IsPSL G 4 2) : False := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  let d := (e.trans (Atlas.fieldEquivPSL 4 a)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4))
  let B := K.map d.toMonoidHom
  let b : K ≃* B := d.subgroupMap K
  have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv b hK
  have hU : (blockU B).map B.subtype = ((blockU K).map K.subtype).map d.toMonoidHom := by
    rw [← RankOne.Solvable.blockU_map_equiv b, map_map, map_map]
    rfl
  apply no_block_in_linear_four B hB
  rw [hU, card_map_of_injective d.injective]
  exact hc

/-- Every alternating row of Theorem C is excluded with the original block. -/
theorem not_alternating_of_alternatingFive
    (K : Subgroup G) (hK : IsAlternatingBlock K 5)
    (hc : Nat.card ((blockU K).map K.subtype) = 16)
    {n : ℕ} (hn : n ≤ 8) (e : G ≃* alternatingGroup (Fin n)) : False := by
  by_cases hn8 : n = 8
  · subst n
    apply not_psl4Two_of_alternatingFive K hK hc
    exact ⟨ZMod 2, inferInstance, inferInstance, by simp,
      ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩⟩
  · have hd := card_dvd_of_alternatingFive K hK hc
    rw [Nat.card_congr e.toEquiv] at hd
    have hd' := hd.trans (alternatingGroup (Fin n)).card_subgroup_dvd_card
    rw [Nat.card_perm, Nat.card_fin] at hd'
    have hn7 : n ≤ 7 := by omega
    interval_cases n <;> norm_num [Nat.factorial] at hd'

/-- The binary degree-five row has Sylow order 1024. -/
theorem sylow_card_of_psl5Two (T : Sylow 2 G)
    (hmodel : ClassicalGroup.IsPSL G 5 2) : Nat.card T = 1024 := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
  norm_num [hcard, Fin.prod_univ_succ] at hc
  have hG : Nat.card G = 9999360 := (Nat.card_congr e.toEquiv).trans hc
  rw [T.card_eq_multiplicity, hG]
  decide +kernel

/-- Both binary linear rows of Theorem C contradict the source block and
its Sylow bound. -/
theorem not_linearBinary_of_alternatingFive
    (K : Subgroup G) (hK : IsAlternatingBlock K 5)
    (hc : Nat.card ((blockU K).map K.subtype) = 16)
    (T : Sylow 2 G) (hT : Nat.card T ≤ 256)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hmodel : ClassicalGroup.IsPSL G n 2) : False := by
  rcases hn with rfl | rfl
  · exact not_psl4Two_of_alternatingFive K hK hc hmodel
  · have := sylow_card_of_psl5Two T hmodel
    omega

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
end
