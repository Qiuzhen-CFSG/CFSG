module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.OppositeRoots

/-!
# Recognizing triality roots by parabolic intersections

The concrete rank-two Tits system classifies the proper strict overgroups of
B as the two original root parabolics. Their two-cell descriptions and the
proved fixed-cell counts give Borel indices q³ + 1 and q + 1.

For either parabolic Q, Q ∩ U⁻ is a two-group, disjoint from B, containing
the literal negative root range. Its order is at most [Q : B]. The root
range has even order [Q : B] − 1, greater than one; parity forces the
intersection to have exactly this order. Thus containment is equality.
This includes q = 2 and avoids additional coordinate or simplicity premises.

Source: Steinberg Theorem 30(1), extended to the twisted groups in Theorem 36,
`refs/KGroup/GLS3/Chapter2St1.tex`; GLS3 2.3.4–8 and §2.4,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace Triality.Standard.OuterOdd.Coverage.RootGeometry.SimpleRecognition
open Parabolics ConcreteBruhat
noncomputable section

private theorem titsSystem_S_pair (f : ℕ) (hf : 0 < f) :
    (titsSystem f hf).S = {simpleReflection f hf .arms, simpleReflection f hf .central} := by
  ext s
  rw [mem_titsSystem_S_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Every proper strict overgroup of the Borel is one of the two root parabolics. -/
theorem eq_parabolic_of_borel_lt (f : ℕ) (hf : 0 < f)
    (H : Subgroup (Carrier (binaryParameters f hf)))
    (hB : borel (binaryParameters f hf) < H) (hH : H ≠ ⊤) :
    ∃ i : Node, H = parabolic (binaryParameters f hf) i := by
  let T := titsSystem f hf
  have hclass := T.subgroup_eq_standardParabolic_simpleIndices H hB.le
  have hI := T.simpleIndices_subset H
  rw [titsSystem_S_pair f hf] at hI
  rcases Set.subset_pair_iff_eq.mp hI with he | he | he | he
  · rw [he, T.standardParabolic_empty] at hclass
    exact (hB.ne hclass.symm).elim
  · exact ⟨.arms, hclass.trans (by rw [he]; exact (parabolic_eq_standardParabolic f hf .arms).symm)⟩
  · exact ⟨.central, hclass.trans (by rw [he]; exact (parabolic_eq_standardParabolic f hf .central).symm)⟩
  · rw [← titsSystem_S_pair f hf] at he
    exact (hH (hclass.trans ((congrArg T.standardParabolic he).trans T.standardParabolic_S))).elim

private theorem parabolic_ne_borel (f : ℕ) (hf : 0 < f) (i : Node) :
    parabolic (binaryParameters f hf) i ≠ borel (binaryParameters f hf) := by
  let T := titsSystem f hf
  have hs : simpleReflection f hf i ∈ T.S := by
    rw [titsSystem_S]
    exact Set.mem_range_self i
  rw [parabolic_eq_standardParabolic f hf i]
  change T.standardParabolic {simpleReflection f hf i} ≠ T.B
  intro h
  have h := h.trans T.standardParabolic_empty.symm
  have he := (T.standardParabolic_eq_iff (Set.singleton_subset_iff.mpr hs)
    (Set.empty_subset _)).mp h
  exact Set.singleton_ne_empty _ he

/-- Borel-preserving automorphisms permute the actual root parabolics. -/
theorem map_parabolic_eq_of_borel_invariant (f : ℕ) (hf : 0 < f)
    (a : MulAut (Carrier (binaryParameters f hf)))
    (ha : (borel (binaryParameters f hf)).map a.toMonoidHom = borel (binaryParameters f hf))
    (i : Node) : ∃ j : Node,
      (parabolic (binaryParameters f hf) i).map a.toMonoidHom =
        parabolic (binaryParameters f hf) j := by
  apply eq_parabolic_of_borel_lt f hf
  · refine lt_of_le_of_ne ?_ ?_
    · rw [← ha]
      exact Subgroup.map_mono (borel_le_parabolic _ i)
    · intro h
      apply parabolic_ne_borel f hf i
      exact Subgroup.map_injective a.injective (h.symm.trans ha.symm)
  · intro h
    apply parabolic_ne_top_binary (binaryParameters f hf) rfl i
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    exact h.trans (Subgroup.map_top_of_surjective a.toMonoidHom a.surjective).symm

private theorem parabolic_carrier (f : ℕ) (hf : 0 < f) (i : Node) :
    (parabolic (binaryParameters f hf) i : Set (Carrier (binaryParameters f hf))) =
      (borel (binaryParameters f hf) : Set _) ∪
        cell (binaryParameters f hf) rfl (relativeReflection i) := by
  ext x
  constructor
  · exact FoldedCellGeometry.parabolic_cell_cover f hf i x
  · intro h
    rcases h with h | h
    · exact borel_le_parabolic _ i h
    · apply (FoldedCellGeometry.mem_parabolic_iff f hf i x).mpr
      exact Or.inr h

private theorem disjoint_borel_simple_cell (f : ℕ) (hf : 0 < f) (i : Node) :
    Disjoint (borel (binaryParameters f hf) : Set (Carrier (binaryParameters f hf)))
      (cell (binaryParameters f hf) rfl (relativeReflection i)) := by
  apply Set.disjoint_left.mpr
  intro x hx hi
  have hx1 : x ∈ cell (binaryParameters f hf) rfl 1 := by
    rw [cell_eq_bruhatCell f hf 1, map_one, (titsSystem f hf).bruhatCell_one]
    exact hx
  have he := FixedDescent.cell_index_unique f hf hx1 hi
  cases i <;> cases he

/-- The Borel index in a root parabolic is the size of its root field plus one. -/
theorem borel_relIndex_parabolic (f : ℕ) (hf : 0 < f) (i : Node) :
    (borel (binaryParameters f hf)).relIndex (parabolic (binaryParameters f hf) i) =
      (match i with | .arms => (binaryParameters f hf).q ^ 3
                    | .central => (binaryParameters f hf).q) + 1 := by
  let P := binaryParameters f hf
  have hcard : Nat.card (parabolic P i) = Nat.card (borel P) *
      ((match i with | .arms => P.q ^ 3 | .central => P.q) + 1) := by
    change Set.ncard (parabolic P i : Set (Carrier P)) = _
    rw [parabolic_carrier f hf i,
      Set.ncard_union_eq (disjoint_borel_simple_cell f hf i)]
    change Nat.card (borel P) + Nat.card {x : Carrier P // x ∈ cell P rfl (relativeReflection i)} = _
    rw [FixedCellCount.card_cell f hf]
    have hpow : P.q ^ FixedCellCount.inversionCount (relativeReflection i) =
        (match i with | .arms => P.q ^ 3 | .central => P.q) := by
      cases i <;> simp [relativeReflection, FixedCellCount.inversionCount_table]
    rw [hpow]
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    rfl
  have hmul := ((borel P).subgroupOf (parabolic P i)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (borel_le_parabolic P i)).toEquiv] at hmul
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := borel P)) (hmul.trans hcard)

/-- A two-subgroup disjoint from B fits in the B-cosets; an even subset of
size one less than their number therefore exhausts that subgroup. -/
private theorem root_intersection_of_index {G : Type*} [Group G] [Finite G]
    (B Q V : Subgroup G) (S : Set G) (hBV : Disjoint B V)
    (hV : IsPGroup 2 V) (hS : S ⊆ (Q ⊓ V : Subgroup G))
    (hcard : 1 < Nat.card S) (heven : Even (Nat.card S))
    (hindex : B.relIndex Q = Nat.card S + 1) :
    S = (Q ⊓ V : Subgroup G) := by
  have hdis : B ⊓ (Q ⊓ V) = ⊥ :=
    disjoint_iff.mp (hBV.mono_right inf_le_right)
  have hbound := Subgroup.relIndex_le_of_le_right
    (H := B) (K := Q ⊓ V) (L := Q) inf_le_left (by rw [hindex]; omega)
  rw [← Subgroup.inf_relIndex_right B (Q ⊓ V), hdis,
    Subgroup.relIndex_bot_left, hindex] at hbound
  have hlower : Nat.card S ≤ Nat.card ↥(Q ⊓ V) := Set.ncard_le_ncard hS
  have hI : IsPGroup 2 ↥(Q ⊓ V) :=
    hV.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  have hdiv : 2 ∣ Nat.card ↥(Q ⊓ V) := hI.card_eq_or_dvd.resolve_left (by omega)
  have hseven := even_iff_two_dvd.mp heven
  exact Set.eq_of_subset_of_ncard_le hS (by
    change Nat.card ↥(Q ⊓ V) ≤ Nat.card S
    omega)

/-- The source intersection uses the original full parabolic and the literal
negative folded root parametrization, with no small-field exception. -/
theorem negative_range_eq_intersection (f : ℕ) (hf : 0 < f) (i : Node) :
    Set.range (rootElement (binaryParameters f hf) rfl false i) =
      (parabolic (binaryParameters f hf) i ⊓
        oppositeUnipotent (binaryParameters f hf) rfl : Subgroup _) := by
  let P := binaryParameters f hf
  apply root_intersection_of_index (borel P) (parabolic P i)
    (oppositeUnipotent P rfl) _ (disjoint_borel_opposite f hf)
    ((unipotent_isPGroup_binary P rfl).map
      (MulAut.conj (weylRepresentative P rfl (.r 3))).toMonoidHom)
  · rintro x ⟨t, rfl⟩
    exact ⟨negative_mem_parabolic P rfl i t, negative_mem_opposite f hf i t⟩
  · rw [card_root_range (binaryParameters f hf) (binaryParameters_prime f hf) false i]
    have hq : 1 < P.q := by have := P.q_ge_two; omega
    cases i
    · exact one_lt_pow₀ hq (by decide)
    · exact hq
  · rw [card_root_range (binaryParameters f hf) (binaryParameters_prime f hf) false i]
    have hq : Even P.q := by
      change Even (2 ^ f)
      exact even_two.pow_of_ne_zero (by omega)
    cases i
    · exact hq.pow_of_ne_zero (by decide)
    · exact hq
  · rw [card_root_range (binaryParameters f hf) (binaryParameters_prime f hf) false i]
    exact borel_relIndex_parabolic f hf i

end
end Triality.Standard.OuterOdd.Coverage.RootGeometry.SimpleRecognition
