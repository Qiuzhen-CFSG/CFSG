module

public import Theory.Mathieu.M22.WittDesign
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.Graph
public import Mathlib.Data.Nat.Bitwise

/-!
# Comparing the native Witt construction with the exact ATLAS graph

The vertices are the root, the native 22 Mathieu points, and the actual
77 hexads in `m22Blocks`. A checked finite relabeling identifies these
vertices with the fixed degree-100 ATLAS coordinates. Kernel-checked
incidence-bit calculations verify root--point, point--hexad, and disjoint
hexad edges. The mask-disjointness argument is structural; the certificates
only evaluate the small incidence masks and the existing adjacency rows.

The relabeling was found by simultaneous partition refinement of the two
100-vertex graphs. Its inverse and every required edge implication are
proved here, so the search is not a proof premise. These facts are consumed
by `GraphComparison`, which supplies the reverse edge implication using the
already proved common degree 22.

Source: the native Witt construction of Higman and Sims, Math. Z. 105
(1968), 110--113, as used in Wales, Pacific J. Math. 30 (1969), p.274.
The exact permutation model and its ATLAS attribution are in
`Theory/SpecificGroups/LeechRelated/AtlasCarriers/HS.lean`.
-/

public section
namespace Sporadic.LeechRelated.HS.WittModel
open Sporadic.Mathieu
open NormalizerIndex OrderCertificate
noncomputable section

/-- The native Witt vertices, with the actual Mathieu hexads. -/
abbrev Vertex := Unit ⊕ (Fin 22 ⊕ {B // B ∈ m22Blocks})

private def blockMap (i : Fin 77) : {B // B ∈ m22Blocks} :=
  ⟨m22BlockAt i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

private theorem blockMap_bijective : Function.Bijective blockMap := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, ?_⟩
  · intro B
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp B.property
    exact ⟨i, Subtype.ext hi⟩
  · simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_subtype,
      Finset.filter_mem_eq_inter, Finset.univ_inter, m22Blocks_cardinality]

/-- The checked enumeration of native hexads. -/
def blockEquiv : Fin 77 ≃ {B // B ∈ m22Blocks} :=
  Equiv.ofBijective blockMap blockMap_bijective

@[simp] theorem blockEquiv_val (i : Fin 77) : (blockEquiv i).val = m22BlockAt i := by rfl

private def encode : Unit ⊕ (Fin 22 ⊕ Fin 77) → Fin 100
  | .inl _ => 0
  | .inr (.inl a) => ⟨a.val + 1, by omega⟩
  | .inr (.inr b) => ⟨b.val + 23, by omega⟩

private theorem encode_bijective : Function.Bijective encode := by
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, by simp⟩
  intro x
  by_cases hx : x.val = 0
  · exact ⟨.inl (), Fin.ext hx.symm⟩
  by_cases ha : x.val < 23
  · refine ⟨.inr (.inl ⟨x.val - 1, by omega⟩), Fin.ext ?_⟩
    change x.val - 1 + 1 = x.val
    omega
  · refine ⟨.inr (.inr ⟨x.val - 23, by omega⟩), Fin.ext ?_⟩
    change x.val - 23 + 23 = x.val
    omega

private def encodeEquiv : Unit ⊕ (Fin 22 ⊕ Fin 77) ≃ Fin 100 :=
  Equiv.ofBijective encode encode_bijective

private def relabel (x : Fin 100) : Fin 100 :=
  ⟨(2656412689081589609763440593357672123970468210023665748832166131305573980903608287611119642000139668041008701315642873290539242036622277777939259856390320881038107809225909633623678398725163575454288771767468544 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def unlabel (x : Fin 100) : Fin 100 :=
  ⟨(1503982624748169372947131403701580843058362835680756517296092200422940130548588686479939313939496889362822284593178000676488653179007678289485975320647549640440644776176550685008503881088330881356905556962877312 >>> (7 * x.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩


private theorem relabel_left : ∀ x, unlabel (relabel x) = x := by
  apply allFin
  decide +kernel

private theorem relabel_right : ∀ x, relabel (unlabel x) = x := by
  apply allFin
  decide +kernel

private def relabelEquiv : Equiv.Perm (Fin 100) where
  toFun := relabel
  invFun := unlabel
  left_inv := relabel_left
  right_inv := relabel_right

/-- A literal bijection to the ATLAS degree-100 vertices. -/
def modelEquiv : Vertex ≃ Fin 100 :=
  (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr (Equiv.refl (Fin 22)) blockEquiv.symm)).trans
    (encodeEquiv.trans relabelEquiv)

private theorem root_point_check : ∀ i : Fin 22,
    adjacency (relabel 0) (relabel ⟨i.val + 1, by omega⟩) := by
  apply allFin
  decide +kernel

private theorem point_block_check : ∀ i : Fin 22, ∀ j : Fin 77,
    (m22BlockMask j).testBit i.val = true →
      adjacency (relabel ⟨i.val + 1, by omega⟩) (relabel ⟨j.val + 23, by omega⟩) := by
  apply allFin
  decide +kernel

private theorem block_block_check : ∀ i j : Fin 77,
    m22BlockMask i &&& m22BlockMask j = 0 →
      adjacency (relabel ⟨i.val + 23, by omega⟩) (relabel ⟨j.val + 23, by omega⟩) := by
  apply allFin
  decide +kernel

private theorem mask_bound : ∀ i : Fin 77, m22BlockMask i < 2 ^ 22 := by
  apply allFin
  decide +kernel

private theorem mask_disjoint (i j : Fin 77) (hd : Disjoint (m22BlockAt i) (m22BlockAt j)) :
    m22BlockMask i &&& m22BlockMask j = 0 := by
  apply Nat.zero_of_testBit_eq_false
  intro k
  rw [Nat.testBit_land]
  by_cases hk : k < 22
  · have hn : ¬ ((m22BlockMask i).testBit k = true ∧ (m22BlockMask j).testBit k = true) := by
      rintro ⟨hi, hj⟩
      have hi' : (⟨k, hk⟩ : Fin 22) ∈ m22BlockAt i :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      have hj' : (⟨k, hk⟩ : Fin 22) ∈ m22BlockAt j :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      exact Finset.disjoint_left.mp hd hi' hj'
    simpa only [Bool.and_eq_false_iff, Bool.not_eq_true] using not_and_or.mp hn
  · have hi : (m22BlockMask i).testBit k = false := Nat.testBit_eq_false_of_lt
      ((mask_bound i).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hi, Bool.false_and]

/-- Root-to-point edges agree with the literal ATLAS adjacency. -/
theorem root_point (i : Fin 22) :
    adjacency (modelEquiv (.inl ())) (modelEquiv (.inr (.inl i))) := root_point_check i

/-- Point-to-hexad incidence gives literal ATLAS edges. -/
theorem point_block (i : Fin 22) (B : {B // B ∈ m22Blocks}) (hi : i ∈ B.val) :
    adjacency (modelEquiv (.inr (.inl i))) (modelEquiv (.inr (.inr B))) := by
  obtain ⟨j, rfl⟩ := blockEquiv.surjective B
  have hbit : (m22BlockMask j).testBit i.val = true := (Finset.mem_filter.mp hi).2
  simpa [modelEquiv, Equiv.sumCongr, encodeEquiv, encode, relabelEquiv] using point_block_check i j hbit

/-- Disjoint hexads give literal ATLAS edges. -/
theorem block_block (B C : {B // B ∈ m22Blocks}) (hd : Disjoint B.val C.val) :
    adjacency (modelEquiv (.inr (.inr B))) (modelEquiv (.inr (.inr C))) := by
  obtain ⟨i, rfl⟩ := blockEquiv.surjective B
  obtain ⟨j, rfl⟩ := blockEquiv.surjective C
  have hm := mask_disjoint i j hd
  simpa [modelEquiv, Equiv.sumCongr, encodeEquiv, encode, relabelEquiv] using block_block_check i j hm

end
end Sporadic.LeechRelated.HS.WittModel
