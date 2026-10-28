module
public import Mathlib.Data.BitVec
public import Mathlib.Tactic

/-!
# Ten points in the binary four-space

Every subset of at least ten nonzero vectors in F₂⁴ contains a basis
v₀,v₁,v₂,v₃ and all three sums v₀+vⱼ for j ≠ 0. We state this using
the multiplicative type tag, for direct use with elementary abelian groups.

A finite certificate lists 135 configurations. The first kernel computation
checks that each subset of the fifteen nonzero points having at least ten
points contains one listed configuration. The second checks membership of the
seven required points and gives all sixteen vectors as products of the four
generators. Neither coverage nor generation is assumed. The bit-mask encoding
and its cardinality are proved below, connecting both computations to sets.

This source-independent finite geometry supplies the larger-orbit alternative
in Parrott, *A characterization of the Tits' simple group* (1972), Lemma 4,
printed pp.674–675. It requires no classification of automorphism groups.
-/

namespace Theory.ElementaryAbelian

private def configs : List (Fin 65536 × (Fin 16 × Fin 16 × Fin 16 × Fin 16)) := [
  (830, 1, 3, 5, 9),
  (54294, 14, 10, 12, 15),
  (3278, 1, 3, 7, 11),
  (59434, 14, 11, 13, 15),
  (12530, 1, 5, 7, 13),
  (16130, 1, 9, 11, 13),
  (29004, 14, 8, 12, 13),
  (27284, 9, 11, 13, 14),
  (39524, 9, 11, 12, 15),
  (42584, 9, 10, 13, 15),
  (22184, 9, 10, 12, 14),
  (19824, 14, 8, 10, 11),
  (33254, 7, 5, 6, 15),
  (50072, 7, 4, 14, 15),
  (26306, 7, 6, 13, 14),
  (7452, 8, 10, 11, 12),
  (46124, 15, 10, 12, 13),
  (19274, 8, 9, 11, 14),
  (43412, 15, 8, 11, 13),
  (55472, 11, 12, 14, 15),
  (42290, 5, 4, 13, 15),
  (4004, 2, 7, 10, 11),
  (55104, 6, 12, 14, 15),
  (29222, 12, 9, 13, 14),
  (47242, 12, 11, 13, 15),
  (10364, 6, 4, 5, 13),
  (26024, 13, 8, 10, 14),
  (33494, 6, 4, 7, 15),
  (13764, 10, 8, 12, 13),
  (19994, 10, 9, 11, 14),
  (13208, 4, 7, 12, 13),
  (39272, 3, 6, 11, 15),
  (17628, 4, 6, 7, 14),
  (60224, 6, 13, 14, 15),
  (4730, 5, 4, 6, 12),
  (53642, 15, 8, 12, 14),
  (23714, 11, 10, 12, 14),
  (44114, 11, 10, 13, 15),
  (21300, 12, 8, 9, 14),
  (43534, 2, 3, 11, 15),
  (7632, 12, 8, 10, 11),
  (28950, 12, 8, 13, 14),
  (18668, 5, 6, 7, 14),
  (34634, 9, 8, 10, 15),
  (41890, 8, 9, 13, 15),
  (38450, 5, 4, 12, 15),
  (7052, 11, 8, 9, 12),
  (49214, 1, 3, 5, 15),
  (42596, 15, 9, 10, 13),
  (27074, 6, 7, 13, 14),
  (58508, 13, 10, 14, 15),
  (15444, 6, 4, 12, 13),
  (36134, 10, 8, 11, 15),
  (61604, 2, 7, 14, 15),
  (15464, 6, 5, 12, 13),
  (53834, 15, 9, 12, 14),
  (10160, 13, 8, 9, 10),
  (24824, 3, 6, 7, 14),
  (25944, 14, 8, 10, 13),
  (7814, 11, 9, 10, 12),
  (5244, 6, 4, 5, 12),
  (47888, 4, 12, 13, 15),
  (35002, 4, 5, 7, 15),
  (20006, 11, 9, 10, 14),
  (50004, 6, 4, 14, 15),
  (16854, 6, 4, 7, 14),
  (12494, 1, 3, 7, 13),
  (50834, 14, 9, 10, 15),
  (38312, 15, 8, 10, 12),
  (31520, 5, 12, 13, 14),
  (47174, 13, 11, 12, 15),
  (21774, 2, 3, 10, 14),
  (9404, 7, 4, 5, 13),
  (11030, 9, 8, 11, 13),
  (36428, 9, 10, 11, 15),
  (45680, 9, 12, 13, 15),
  (45338, 12, 8, 13, 15),
  (39572, 11, 9, 12, 15),
  (18614, 5, 4, 7, 14),
  (34694, 8, 9, 10, 15),
  (54314, 15, 10, 12, 14),
  (25956, 8, 10, 13, 14),
  (50744, 10, 9, 14, 15),
  (32384, 7, 12, 13, 14),
  (6362, 7, 4, 6, 12),
  (1010, 1, 5, 7, 9),
  (17126, 7, 5, 6, 14),
  (11744, 13, 8, 10, 11),
  (5930, 9, 8, 10, 12),
  (51874, 14, 9, 11, 15),
  (57884, 13, 9, 14, 15),
  (53712, 8, 12, 14, 15),
  (36122, 11, 8, 10, 15),
  (11050, 8, 9, 11, 13),
  (15410, 1, 5, 11, 13),
  (5910, 8, 9, 10, 12),
  (26126, 3, 2, 10, 14),
  (33212, 7, 4, 5, 15),
  (44084, 15, 10, 11, 13),
  (40136, 12, 10, 11, 15),
  (50024, 6, 5, 14, 15),
  (51554, 14, 8, 11, 15),
  (19244, 11, 8, 9, 14),
  (14648, 8, 11, 12, 13),
  (8890, 4, 5, 7, 13),
  (26894, 3, 2, 11, 14),
  (38594, 6, 7, 12, 15),
  (20724, 2, 6, 7, 14),
  (43672, 4, 7, 13, 15),
  (53574, 14, 8, 12, 15),
  (9446, 7, 5, 6, 13),
  (6938, 8, 9, 11, 12),
  (9434, 7, 4, 6, 13),
  (64514, 1, 11, 13, 15),
  (38292, 8, 10, 12, 15),
  (21912, 4, 7, 12, 14),
  (43624, 6, 5, 13, 15),
  (59468, 13, 11, 14, 15),
  (22884, 14, 8, 11, 12),
  (13220, 5, 7, 12, 13),
  (25544, 14, 8, 9, 13),
  (36464, 15, 9, 10, 11),
  (34934, 4, 5, 6, 15),
  (30854, 12, 11, 13, 14),
  (30794, 13, 11, 12, 14),
  (13730, 13, 8, 10, 12),
  (11804, 9, 10, 11, 13),
  (42644, 13, 9, 10, 15),
  (28424, 3, 10, 11, 14),
  (45350, 13, 8, 12, 15),
  (17594, 4, 5, 7, 14),
  (21330, 8, 9, 12, 14),
  (14930, 13, 9, 11, 12),
  (13620, 8, 10, 12, 13),
  (2552, 3, 6, 7, 11)]


private def pop : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, m => m % 2 + pop n (m / 2)


private abbrev Model := Multiplicative (Fin 4 → ZMod 2)
private def vec (n : Fin 16) : Model :=
  Multiplicative.ofAdd fun i => if (BitVec.ofFin n).getLsb i then 1 else 0

private theorem vec_bijective : Function.Bijective vec := by decide +kernel

private def cfg (c : Fin 65536 × (Fin 16 × Fin 16 × Fin 16 × Fin 16)) : Fin 4 → Fin 16 :=
  ![c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2]


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private theorem cover : ∀ s : Fin 256, ∀ t : Fin 128,
    10 ≤ pop 15 (s.val + 256 * t.val) →
    (configs.any fun c => ((s.val + 256 * t.val) * 2) &&& c.1.val == c.1.val) = true := by
  decide +kernel


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private theorem sound : (configs.all fun c => decide (
    (∀ i, (BitVec.ofFin c.1 : BitVec 16).getLsb (cfg c i) = true) ∧
    (∀ j : Fin 4, j ≠ 0 → ∃ n : Fin 16,
      (BitVec.ofFin c.1 : BitVec 16).getLsb n = true ∧
      vec n = vec (cfg c 0) * vec (cfg c j)) ∧
    (∀ n : Fin 16, ∃ t : Fin 16,
      vec n = ∏ i : Fin 4, if (BitVec.ofFin t : BitVec 4).getLsb i then
        vec (cfg c i) else 1))) = true := by
  decide +kernel

private theorem pop_card {n : ℕ} (x : BitVec n) :
    pop n x.toNat = (Finset.univ.filter fun i : Fin n => x.getLsb i = true).card := by
  induction x using BitVec.concat_induction with
  | nil => rfl
  | concat bv b ih =>
    rw [Fin.card_filter_univ_succ']
    simp only [BitVec.getLsb_eq_getElem, BitVec.toNat_concat, pop]
    simp only [BitVec.getLsb_eq_getElem] at ih
    cases b <;>
      simp [BitVec.getElem_concat_zero, BitVec.getElem_concat_succ, Nat.add_mod, Nat.add_div] <;>
      exact ih

private def mask (s : Finset (Fin 16)) : BitVec 16 :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 16 => decide (i ∈ s))).cast (by simp)

private theorem mask_bit (s : Finset (Fin 16)) (i : Fin 16) :
    (mask s).getLsb i = decide (i ∈ s) := by
  fin_cases i <;> simp [mask, ← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofBoolListLE]


private theorem mask_card (s : Finset (Fin 16)) : pop 16 (mask s).toNat = s.card := by
  rw [pop_card]
  simp only [mask_bit, decide_eq_true_eq]
  congr 1
  ext i
  simp

private theorem mask_even (s : Finset (Fin 16)) (h : (0 : Fin 16) ∉ s) :
    (mask s).toNat % 2 = 0 := by
  have hb := mask_bit s 0
  change (mask s).toNat.testBit 0 = decide ((0 : Fin 16) ∈ s) at hb
  simp only [Nat.testBit_zero, h, decide_false, decide_eq_false_iff_not] at hb
  omega

private theorem mask_inclusion (s : Finset (Fin 16)) (c : Fin 65536)
    (h : (mask s).toNat &&& c.val = c.val) (i : Fin 16)
    (hc : (BitVec.ofFin c : BitVec 16).getLsb i = true) : i ∈ s := by
  have hi := congrArg (fun n : ℕ => n.testBit i) h
  rw [Nat.testBit_and] at hi
  change ((mask s).getLsb i && (BitVec.ofFin c : BitVec 16).getLsb i) =
    (BitVec.ofFin c : BitVec 16).getLsb i at hi
  rw [hc, Bool.and_true, mask_bit] at hi
  exact of_decide_eq_true hi

private theorem find_config
    (s : Finset (Fin 16)) (hzero : 0 ∉ s) (hcard : 10 ≤ s.card) :
    ∃ c : Fin 65536 × (Fin 16 × Fin 16 × Fin 16 × Fin 16),
       (∀ i, cfg c i ∈ s) ∧
       (∀ j : Fin 4, j ≠ 0 → ∃ n ∈ s, vec n = vec (cfg c 0) * vec (cfg c j)) ∧
       (∀ n : Fin 16, ∃ t : Fin 16,
          vec n = ∏ i : Fin 4, if (BitVec.ofFin t : BitVec 4).getLsb i then
            vec (cfg c i) else 1) := by
  let m := (mask s).toNat / 2
  have hbound : (mask s).toNat < 65536 := (mask s).isLt
  have hm : m < 32768 := by dsimp [m]; omega
  let a : Fin 256 := ⟨m % 256, Nat.mod_lt _ (by decide)⟩
  let b : Fin 128 := ⟨m / 256, by omega⟩
  have hab : a.val + 256 * b.val = m := Nat.mod_add_div _ _
  have heven := mask_even s hzero
  have htwice : m * 2 = (mask s).toNat := by dsimp [m]; omega
  have hpop : 10 ≤ pop 15 (a.val + 256 * b.val) := by
    rw [hab]
    have hcount := mask_card s
    rw [pop, heven, zero_add] at hcount
    exact hcount ▸ hcard
  obtain ⟨c, hc, hmask⟩ := List.any_eq_true.mp (cover a b hpop)
  have hmask' : (mask s).toNat &&& c.1.val = c.1.val := by
    simpa only [hab, htwice] using (of_decide_eq_true hmask)
  obtain ⟨hi, hp, hg⟩ := of_decide_eq_true (List.all_eq_true.mp sound c hc)
  refine ⟨c, fun i => mask_inclusion s c.1 hmask' _ (hi i), ?_, hg⟩
  intro j hj
  obtain ⟨n, hn, he⟩ := hp j hj
  exact ⟨n, mask_inclusion s c.1 hmask' n hn, he⟩

/-- Every set of at least ten nonidentity points of the binary four-space contains
four generators and the three products with the first generator. -/
public theorem binary_four_exists_generating_configuration
    (S : Set (Multiplicative (Fin 4 → ZMod 2))) (hzero : 1 ∉ S)
    (hcard : 10 ≤ S.ncard) :
    ∃ v : Fin 4 → Multiplicative (Fin 4 → ZMod 2), Subgroup.closure (Set.range v) = ⊤ ∧
      (∀ i, v i ∈ S) ∧ (∀ j : Fin 4, j ≠ 0 → v 0 * v j ∈ S) := by
  classical
  let s := (vec ⁻¹' S).toFinset
  have hs0 : (0 : Fin 16) ∉ s := by
    intro hz
    have hh : vec 0 ∈ S := (Set.mem_toFinset (s := vec ⁻¹' S)).mp hz
    exact hzero ((show vec 0 = 1 by decide +kernel) ▸ hh)
  have hscard : 10 ≤ s.card := by
    have hc := Set.ncard_preimage_of_injective_subset_range (s := S) vec_bijective.1
      (by rw [vec_bijective.2.range_eq]; exact Set.subset_univ _)
    rw [Set.ncard_eq_toFinset_card'] at hc
    exact hc ▸ hcard
  obtain ⟨c, hi, hp, hg⟩ := find_config s hs0 hscard
  refine ⟨fun i => vec (cfg c i), ?_, ?_, ?_⟩
  · apply top_unique
    intro y _
    obtain ⟨n, rfl⟩ := vec_bijective.2 y
    obtain ⟨t, ht⟩ := hg n
    rw [ht]
    apply Subgroup.prod_mem
    intro i _
    split_ifs
    · exact Subgroup.subset_closure ⟨i, rfl⟩
    · exact Subgroup.one_mem _
  · intro i
    exact (Set.mem_toFinset (s := vec ⁻¹' S)).mp (hi i)
  · intro j hj
    obtain ⟨n, hn, he⟩ := hp j hj
    rw [← he]
    exact (Set.mem_toFinset (s := vec ⁻¹' S)).mp hn

end Theory.ElementaryAbelian
