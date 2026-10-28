module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.PrimitiveRecognition.LargeDegree.Definitions

/-!
# Pair-intersection proof of the primitive degree bound

Assuming the two local permutation inputs in `LargeDegree.Definitions`,
this module proves the complete large-degree exclusion. With five disjoint
pairs, even intersection of every translated four-set with each union of
two pairs forces the two members of a pair to be inseparable by translates.
Rudio's theorem contradicts primitivity. In degree nine, four pairs cover
eight points; even intersection forces every translated four-set to avoid
the remaining point, contradicting transitivity.

The final source adapter uses the actual Sylow subgroup, literal permutation
image and inherited action. It remains conditional until the local
Klein-group calculation and simultaneous Sylow placement are proved.
Source: the alternating-overgroup step of Aschbacher–Smith B.1.13,
printed p.74 (PDF p.85).
-/

public section
open Equiv MulAction
open scoped BigOperators Pointwise

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.LargeDegree

variable {α : Type*} [DecidableEq α] {k : ℕ}

private def pair (f : (Fin k × Fin 2) ↪ α) (i : Fin k) : Finset α :=
  {f (i, 0), f (i, 1)}

private theorem pair_disjoint (f : (Fin k × Fin 2) ↪ α) {i j : Fin k} (hij : i ≠ j) :
    Disjoint (pair f i) (pair f j) := by
  simp only [pair, Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
  intro a ha hb
  rcases ha with rfl | rfl <;> rcases hb with h | h <;>
    exact hij (congrArg Prod.fst (f.injective h))

private theorem sum_pair_inter_le (f : (Fin k × Fin 2) ↪ α) (B : Finset α) :
    ∑ i : Fin k, (B ∩ pair f i).card ≤ B.card := by
  have hd : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i => B ∩ pair f i) := by
    intro i _ j _ hij
    exact (pair_disjoint f hij).mono Finset.inter_subset_right Finset.inter_subset_right
  rw [← Finset.card_biUnion hd]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  exact (Finset.mem_inter.mp hi).1

private theorem even_pair_union_iff (f : (Fin k × Fin 2) ↪ α) (B : Finset α)
    {i j : Fin k} (hij : i ≠ j) :
    Even ((B ∩ (pair f i ∪ pair f j)).card) ↔
      Even ((B ∩ pair f i).card + (B ∩ pair f j).card) := by
  rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint]
  exact (pair_disjoint f hij).mono Finset.inter_subset_right Finset.inter_subset_right

private theorem five_pairs_not_separated (f : (Fin 5 × Fin 2) ↪ α) (B : Finset α)
    (hB : B.card = 4)
    (he : ∀ i j : Fin 5, i ≠ j → Even ((B ∩ (pair f i ∪ pair f j)).card)) :
    f (0, 0) ∈ B ↔ f (0, 1) ∈ B := by
  have hsum := sum_pair_inter_le f B
  rw [hB] at hsum
  norm_num [Fin.sum_univ_succ] at hsum
  change (B ∩ pair f 0).card + ((B ∩ pair f 1).card +
    ((B ∩ pair f 2).card + ((B ∩ pair f 3).card + (B ∩ pair f 4).card))) ≤ 4 at hsum
  have h01 := (even_pair_union_iff f B (by decide : (0 : Fin 5) ≠ 1)).mp
    (he 0 1 (by decide))
  have h02 := (even_pair_union_iff f B (by decide : (0 : Fin 5) ≠ 2)).mp
    (he 0 2 (by decide))
  have h03 := (even_pair_union_iff f B (by decide : (0 : Fin 5) ≠ 3)).mp
    (he 0 3 (by decide))
  have h04 := (even_pair_union_iff f B (by decide : (0 : Fin 5) ≠ 4)).mp
    (he 0 4 (by decide))
  rw [Nat.even_iff] at h01 h02 h03 h04
  have hnot : (B ∩ pair f 0).card ≠ 1 := by omega
  constructor
  · intro ha
    by_contra hb
    apply hnot
    have heq : B ∩ pair f 0 = {f (0, 0)} := by
      ext x
      simp only [Finset.mem_inter, pair, Finset.mem_insert, Finset.mem_singleton]
      aesop
    simp [heq]
  · intro hb
    by_contra ha
    apply hnot
    have heq : B ∩ pair f 0 = {f (0, 1)} := by
      ext x
      simp only [Finset.mem_inter, pair, Finset.mem_insert, Finset.mem_singleton]
      aesop
    simp [heq]

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.LargeDegree

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.LargeDegree
open scoped BigOperators Pointwise
variable {α : Type*} [DecidableEq α] {k : ℕ}

private theorem sum_pair_inter_eq (f : (Fin k × Fin 2) ↪ α) (B : Finset α) :
    ∑ i : Fin k, (B ∩ pair f i).card =
      (B ∩ Finset.univ.map f).card := by
  have hd : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i => B ∩ pair f i) := by
    intro i _ j _ hij
    exact (pair_disjoint f hij).mono Finset.inter_subset_right Finset.inter_subset_right
  rw [← Finset.card_biUnion hd]
  congr 1
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter,
    pair, Finset.mem_insert, Finset.mem_singleton, Finset.mem_map]
  constructor
  · rintro ⟨i, hx, rfl | rfl⟩
    · exact ⟨hx, (i, 0), rfl⟩
    · exact ⟨hx, (i, 1), rfl⟩
  · rintro ⟨hx, ⟨i, b⟩, h⟩
    fin_cases b
    · exact ⟨i, hx, Or.inl h.symm⟩
    · exact ⟨i, hx, Or.inr h.symm⟩

private theorem four_pairs_cover (f : (Fin 4 × Fin 2) ↪ Fin 9) (B : Finset (Fin 9))
    (hB : B.card = 4)
    (he : ∀ i j : Fin 4, i ≠ j → Even ((B ∩ (pair f i ∪ pair f j)).card)) :
    B ⊆ Finset.univ.map f := by
  have h01 := (even_pair_union_iff f B (by decide : (0 : Fin 4) ≠ 1)).mp
    (he 0 1 (by decide))
  have h23 := (even_pair_union_iff f B (by decide : (2 : Fin 4) ≠ 3)).mp
    (he 2 3 (by decide))
  have hsum := sum_pair_inter_eq f B
  norm_num [Fin.sum_univ_succ] at hsum
  change (B ∩ pair f 0).card + ((B ∩ pair f 1).card +
    ((B ∩ pair f 2).card + (B ∩ pair f 3).card)) = _ at hsum
  have hcard : (Finset.univ.map f).card = 8 := by simp
  have hcompl : (Finset.univ \ Finset.univ.map f).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hcard]
  have hle : (B \ Finset.univ.map f).card ≤ 1 := by
    rw [← hcompl]
    exact Finset.card_le_card (Finset.sdiff_subset_sdiff (Finset.subset_univ B) le_rfl)
  have hsplit := Finset.card_sdiff_add_card_inter B (Finset.univ.map f)
  rw [Nat.even_iff] at h01 h23
  have hzero : (B \ Finset.univ.map f).card = 0 := by omega
  exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hzero)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.LargeDegree

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.LargeDegree
open scoped BigOperators Pointwise
variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem five_pairs_not_preprimitive (G : Subgroup (Perm α))
    (hp : IsPreprimitive G α) (hα : 4 < Fintype.card α)
    (f : (Fin 5 × Fin 2) ↪ α) (B : Finset α) (hB : B.card = 4)
    (he : ∀ (g : G) (i j : Fin 5), i ≠ j →
      Even (((B.image g.val) ∩ (pair f i ∪ pair f j)).card)) : False := by
  let := hp
  have hne : (B : Set α).Nonempty := Finset.coe_nonempty.mpr
    (Finset.card_pos.mp (by omega))
  have hproper : (B : Set α) ≠ Set.univ := by
    intro h
    have : B = Finset.univ := Finset.coe_injective (by simpa using h)
    have : B.card = Fintype.card α := by rw [this, Finset.card_univ]
    omega
  have hab : f (0, 0) ≠ f (0, 1) := fun h => by
    have := f.injective h
    simp at this
  obtain ⟨g, ha, hb⟩ := IsPreprimitive.exists_mem_smul_and_notMem_smul
    (G := G) B.finite_toSet hne hproper hab
  have himage : (↑(B.image g.val) : Set α) = g • (B : Set α) := by
    rw [Finset.coe_image]
    rfl
  have ha' : f (0, 0) ∈ B.image g.val := by
    change f (0, 0) ∈ (↑(B.image g.val) : Set α)
    rwa [himage]
  have hb' : f (0, 1) ∉ B.image g.val := by
    change f (0, 1) ∉ (↑(B.image g.val) : Set α)
    rwa [himage]
  exact hb' ((five_pairs_not_separated f (B.image g.val)
    ((Finset.card_image_of_injective _ g.val.injective).trans hB) (he g)).mp ha')

private theorem four_pairs_nine_not_pretransitive (G : Subgroup (Perm (Fin 9)))
    (hp : IsPretransitive G (Fin 9))
    (f : (Fin 4 × Fin 2) ↪ Fin 9) (B : Finset (Fin 9)) (hB : B.card = 4)
    (he : ∀ (g : G) (i j : Fin 4), i ≠ j →
      Even (((B.image g.val) ∩ (pair f i ∪ pair f j)).card)) : False := by
  let := hp
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := Finset.univ.map f) (t := Finset.univ) (by simp)
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G b p
  have hmem : p ∈ B.image g.val := by
    exact Finset.mem_image.mpr ⟨b, hb, hg⟩
  exact hp (four_pairs_cover f (B.image g.val)
    ((Finset.card_image_of_injective _ g.val.injective).trans hB) (he g) hmem)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.LargeDegree

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.LargeDegree

private theorem frame_even_intersections (heven : KleinFourOverlapEven)
    {m k : ℕ} (G : Subgroup (Perm (Fin m)))
    (hthree : ∀ g : G, ¬ g.val.IsThreeCycle)
    (F : PairedFrame G k) (B : Finset (Fin m)) (hB : B.card = 4)
    (hfour : KleinFourOn G B) (g : G) (i j : Fin k) (hij : i ≠ j) :
    Even (((B.image g.val) ∩ (pair F.point i ∪ pair F.point j)).card) := by
  have hn : [F.point (i, 0), F.point (i, 1),
      F.point (j, 0), F.point (j, 1)].Nodup := by
    simp [F.point.injective.eq_iff, hij]
  have h := heven m G hthree B hB hfour g _ _ _ _ hn (F.pair_mem i j hij)
  convert h using 1
  congr 2
  ext x
  simp only [pair, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.LargeDegree

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
open LargeDegree

/-- The complete degree-bound deduction from the local odd-intersection
calculation and simultaneous Sylow placement. Both inputs still require
independent proofs; this is not the unconditional source theorem. -/
theorem alternating_primitive_degree_bound_of_pair_geometry
    (heven : KleinFourOverlapEven) (hframes : SylowPairedFrames) :
    AlternatingPrimitiveDegreeBound := by
  intro m _ S X hS _ hp hthree _
  by_contra hm
  have hm9 : 9 ≤ m := by omega
  let G : Subgroup (Perm (Fin m)) := X.map (alternatingGroup (Fin m)).subtype
  have hthreeG : ∀ g : G, ¬ g.val.IsThreeCycle := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, rfl⟩ := hg
    exact hthree ⟨a, ha⟩
  have hpG : IsPreprimitive G (Fin m) := by
    let φ := (alternatingGroup (Fin m)).subtype.subgroupMap X
    let f : Fin m →ₑ[φ] Fin m := { toFun := id, map_smul' _ _ := rfl }
    exact (isPreprimitive_congr (f := f)
      ((alternatingGroup (Fin m)).subtype.subgroupMap_surjective X)
      Function.bijective_id).mp hp
  by_cases hm10 : 10 ≤ m
  · obtain ⟨F, B, hB, hfour⟩ := hframes m 5 (Or.inr rfl) (by omega) S X hS
    exact five_pairs_not_preprimitive G hpG (by simpa using (show 4 < m by omega))
      F.point B hB (frame_even_intersections heven G hthreeG F B hB hfour)
  · have hm : m = 9 := by omega
    subst m
    obtain ⟨F, B, hB, hfour⟩ := hframes 9 4 (Or.inl rfl) (by omega) S X hS
    exact four_pairs_nine_not_pretransitive G hpG.toIsPretransitive F.point B hB
      (frame_even_intersections heven G hthreeG F B hB hfour)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
