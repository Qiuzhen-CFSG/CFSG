module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFactorization
public import Theory.Frattini.Intersection

/-!
# A nonzero module element in the block Sylow Frattini subgroup

A marked transposition in S and the inner pair exchange in R∩K have a
commutator in S∩K whose action is the nonidentity pair diagonal. Its
commutators with U lie both in U and in the derived subgroup of S∩K,
hence in Φ(S∩K). Faithfulness of the marked action makes this intersection
nontrivial. This uses the original block Sylow subgroup and original U.

Source: Aschbacher–Smith, C.5.6(5)–(6), printed p.158.
-/

public section
open Subgroup BinaryPermutation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

/-- The actual block Sylow subgroup contains an element of S inducing the
pair diagonal. It is produced from the marked transposition and exchange. -/
theorem AlternatingPairSetup.exists_diagonal_in_baumann_block
    (h : AlternatingPairSetup R K L) :
    ∃ a : (K ⊔ ChapterB.baumann R : Subgroup G),
      (a : G) ∈ ChapterB.baumann R ⊓ K ∧ h.action a = pairDiagonal := by
  have hs : ChapterB.Offenders.pairSwap 5 0 ∈
      ((ChapterB.baumann R).subgroupOf (K ⊔ ChapterB.baumann R)).map h.action := by
    rw [h.baumann_image]
    exact ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 0 (by decide)
  obtain ⟨s, hs, hsa⟩ := hs
  obtain ⟨r, hr, hra⟩ := h.pairExchange_mem
  have hSR : ⁅ChapterB.baumann R, R⁆ ≤ ChapterB.baumann R :=
    le_normalizer_iff_commutator_le_left.mp
      (R.le_normalizer.trans (Stellmacher.normalizer_le_normalizer_baumann R))
  have hSK : ⁅ChapterB.baumann R, K⁆ ≤ K :=
    le_normalizer_iff_commutator_le_right.mp h.normalizes
  refine ⟨⁅s, r⁆, ⟨hSR (commutator_mem_commutator hs hr.1),
    hSK (commutator_mem_commutator hs hr.2)⟩, ?_⟩
  rw [map_commutatorElement, hsa, hra]
  decide +kernel

/-- The literal module meets the embedded Φ(S∩K) nontrivially. No witness
or nontrivial Frattini subgroup is assumed. -/
theorem AlternatingPairSetup.module_inf_block_frattini_ne_bot
    (h : AlternatingPairSetup R K L) :
    sourceModule K ⊓
      (frattini (ChapterB.baumann R ⊓ K : Subgroup G)).map (ChapterB.baumann R ⊓ K).subtype ≠ ⊥ := by
  let B := ChapterB.baumann R ⊓ K
  have hBR : B ≤ R := inf_le_left.trans inf_le_left
  let : Fact (IsPGroup 2 B) := ⟨h.twoGroup.to_le hBR⟩
  have hUB : sourceModule K ≤ B := le_inf h.module_le (map_subtype_le _)
  have hKU : K ≤ normalizer (sourceModule K : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hKU' : ⁅K, sourceModule K⁆ ≤ sourceModule K :=
    le_normalizer_iff_commutator_le_right.mp hKU
  obtain ⟨a, ha, haa⟩ := h.exists_diagonal_in_baumann_block
  intro hbot
  have hc : (a : G) ∈ centralizer (sourceModule K : Set G) := by
    intro u hu
    have hcommU : ⁅(a : G), u⁆ ∈ sourceModule K :=
      hKU' (commutator_mem_commutator ha.2 hu)
    have hcommPhi : ⁅(a : G), u⁆ ∈ (frattini B).map B.subtype := by
      let aB : B := ⟨a, ha⟩
      let uB : B := ⟨u, hUB hu⟩
      apply mem_map_of_mem B.subtype (x := ⁅aB, uB⁆)
      apply commutator_le_frattini_of_isPGroup (p := 2)
      rw [commutator_def]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    have he : ⁅(a : G), u⁆ = 1 :=
      mem_bot.mp (hbot ▸ show ⁅(a : G), u⁆ ∈ sourceModule K ⊓
        (frattini B).map B.subtype from ⟨hcommU, hcommPhi⟩)
    exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm
  have he : h.action a = 1 := by
    change a ∈ h.action.ker
    rw [h.action_kernel]
    exact hc
  have hd : pairDiagonal ≠ 1 := by decide +kernel
  exact hd (haa.symm.trans he)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
end
