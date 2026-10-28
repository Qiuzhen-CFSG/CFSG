module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.RootIntersections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.DihedralWords
public import Theory.GroupTheory.DoubleCosetCard

/-!
# Literal marked endpoint indices

A singleton standard parabolic is the disjoint union of B and its simple
Bruhat cell. Double-coset counting, together with the unique split Borel
intersection coordinates, gives `[P_s : B] = 1 + [U : U ∩ U^n_s]`.
The conjugation convention is right conjugation; using the inverse simple
representative converts the general double-coset count to that convention.

The endpoint and whole-overlap maps transport these indices to the original
carrier, even when only the quotient is finite. The final paired theorem
also works for an arbitrary original amalgam with its marked isomorphism,
including an amalgam's universal-completion quotient.

Source: Carter §2.5, especially 2.5.9 and the rank-one Bruhat decomposition;
DGS, *Groups and Graphs*, Part II, Theorem D, printed p.224. Identifying the
last index with a simple root-group order still needs the longest-element
factorization; that assertion is not assumed or claimed here.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {X : Type*} [Group X] {T : TitsSystem (X := X)}

private theorem singleton_closure {W : Type*} [Group W] {s w : W} (hs : s ^ 2 = 1) :
    w ∈ closure ({s} : Set W) ↔ w = 1 ∨ w = s := by
  constructor
  · intro hw
    induction hw using closure_induction with
    | mem x hx => exact Or.inr (Set.mem_singleton_iff.mp hx)
    | one => exact Or.inl rfl
    | mul a b ha hb iha ihb =>
      rcases iha with rfl | rfl <;> rcases ihb with rfl | rfl <;> simp_all [pow_two]
    | inv a ha iha =>
      rcases iha with rfl | rfl <;> simp_all [pow_two, mul_eq_one_iff_inv_eq]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact subset_closure (Set.mem_singleton _)

/-- The two literal Bruhat cells in a singleton standard parabolic. -/
theorem singleton_parabolic_cells {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N}
    (hs : s ∈ T.S) : (T.standardParabolic {s} : Set X) = (T.B : Set X) ∪ T.bruhatCell s := by
  ext x
  change x ∈ T.standardParabolic {s} ↔ x ∈ T.B ∨ x ∈ T.bruhatCell s
  rw [T.mem_standardParabolic_iff (Set.singleton_subset_iff.mpr hs)]
  simp only [singleton_closure (T.involutions s hs).2, or_and_right,
    exists_or, exists_eq_left, T.bruhatCell_one]
  rfl

/-- The singleton decomposition is disjoint, so its cardinalities add. -/
theorem singleton_parabolic_card [Finite X]
    {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S) :
    Nat.card (T.standardParabolic {s}) = Nat.card T.B + Nat.card (T.bruhatCell s) := by
  have hd : Disjoint (T.B : Set X) (T.bruhatCell s) := by
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' : x ∈ T.bruhatCell 1 := by rwa [T.bruhatCell_one]
    exact (T.involutions s hs).1 (T.doubleCoset_index_unique hy hx')
  change (T.standardParabolic {s} : Set X).ncard = _
  rw [singleton_parabolic_cells hs, Set.ncard_union_eq hd]
  rfl

/-- Double-coset counting with the fixed right-conjugation convention. -/
theorem simple_cell_card_mul_intersection [Finite X]
    {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S)
    (n : T.N) (hn : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n = s) :
    Nat.card (T.bruhatCell s) *
      Nat.card (T.B ⊓ rightConjugate T.B (n : X) : Subgroup X) =
        Nat.card T.B * Nat.card T.B := by
  have hsInv : s⁻¹ = s := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using (T.involutions s hs).2)
  have hcell : T.bruhatCell s = DoubleCoset.doubleCoset ((n : X)⁻¹) T.B T.B := by
    exact B_mul_representativeSet_mul_B T.B T.N s n⁻¹ (by rw [map_inv, hn, hsInv])
  have hconj : T.B.map (MulAut.conj ((n : X)⁻¹)).toMonoidHom =
      rightConjugate T.B (n : X) := by
    rw [map_equiv_eq_comap_symm']
    ext x
    change (n : X)⁻¹⁻¹ * x * (n : X)⁻¹ ∈ T.B ↔ (n : X) * x * (n : X)⁻¹ ∈ T.B
    rw [inv_inv]
  rw [hcell, ← hconj]
  exact card_doubleCoset_mul_card_inf _ _ _

/-- The exact first rank-one counting recurrence from the split axioms. -/
theorem singleton_parabolic_index [Finite X] (split : SplitData T)
    {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N} (hs : s ∈ T.S)
    (n : T.N) (hn : QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n = s) :
    (T.B.subgroupOf (T.standardParabolic {s})).index =
      1 + ((split.U ⊓ rightConjugate split.U (n : X)).subgroupOf split.U).index := by
  let V := split.U ⊓ rightConjugate split.U (n : X)
  have hB := borel_card split
  have hI := borel_intersection_card split n
  have hC := simple_cell_card_mul_intersection hs n hn
  rw [hI] at hC
  have hV : Nat.card V * (V.subgroupOf split.U).index = Nat.card split.U := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe (show V ≤ split.U from inf_le_left)).toEquiv]
    exact (V.subgroupOf split.U).card_mul_index
  have hBC : Nat.card T.B * (T.B.subgroupOf (T.standardParabolic {s})).index =
      Nat.card (T.standardParabolic {s}) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe (T.B_le_standardParabolic {s})).toEquiv]
    exact (T.B.subgroupOf (T.standardParabolic {s})).card_mul_index
  rw [singleton_parabolic_card hs] at hBC
  have hcell : Nat.card (T.bruhatCell s) = Nat.card T.B * (V.subgroupOf split.U).index := by
    have hp : 0 < Nat.card V * Nat.card (T.B ⊓ T.N : Subgroup X) :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hp
    calc
      _ = Nat.card T.B * Nat.card T.B := hC
      _ = Nat.card T.B * (Nat.card split.U * Nat.card (T.B ⊓ T.N : Subgroup X)) :=
        congrArg (Nat.card T.B * ·) hB
      _ = Nat.card T.B * (V.subgroupOf split.U).index *
          (Nat.card V * Nat.card (T.B ⊓ T.N : Subgroup X)) := by rw [← hV]; ring
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := T.B))
  rw [hBC, hcell, mul_add, mul_one]

variable {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)

/-- The same quotient map transports the full common-Borel inclusion. -/
theorem original_endpoint_index (i : Fin 2) :
    ((P 0 ⊓ P 1).subgroupOf (P i)).index =
      (d.tits.B.subgroupOf (d.tits.standardParabolic {d.simple i})).index := by
  have he : ((P 0 ⊓ P 1).subgroupOf (P i)).map (d.endpointEquiv i).toMonoidHom =
      d.tits.B.subgroupOf (d.tits.standardParabolic {d.simple i}) := by
    apply map_injective (d.tits.standardParabolic {d.simple i}).subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le (d.tits.B_le_standardParabolic _)]
    have hh : (d.tits.standardParabolic {d.simple i}).subtype.comp
        (d.endpointEquiv i).toMonoidHom = d.q.comp (P i).subtype := by
      ext x
      exact d.endpointEquiv_apply i x
    rw [hh, ← map_map]
    have hle : P 0 ⊓ P 1 ≤ P i := by fin_cases i; exact inf_le_left; exact inf_le_right
    rw [map_subgroupOf_eq_of_le hle, d.borel_image]
  rw [← he]
  exact (index_map_of_bijective (d.endpointEquiv i).bijective _).symm

/-- The rank-one recurrence on either original endpoint, with an arbitrary lift. -/
theorem marked_endpoint_index (split : SplitData d.tits) (i : Fin 2)
    (n : d.tits.N)
    (hn : QuotientGroup.mk' ((d.tits.B ⊓ d.tits.N).subgroupOf d.tits.N) n = d.simple i) :
    ((P 0 ⊓ P 1).subgroupOf (P i)).index =
      1 + ((split.U ⊓ rightConjugate split.U (n : X ⧸ d.D)).subgroupOf split.U).index := by
  rw [original_endpoint_index d i]
  exact singleton_parabolic_index split (d.simple_mem i) n hn


open Theory.GroupTheory

/-- The left marked map is the literal inclusion, derived from the public square. -/
theorem standardAmalgam_left_eq_inclusion :
    d.standardAmalgam.left = inclusion (d.tits.B_le_standardParabolic {d.simple 0}) := by
  ext b
  obtain ⟨c, rfl⟩ := d.markedIso.middle.surjective b
  change (d.standardAmalgam.left (d.markedIso.middle c) : X ⧸ d.D) =
    (d.markedIso.middle c : X ⧸ d.D)
  rw [← d.markedIso.left_commutes, d.markedIso_left_apply, d.markedIso_middle_apply]
  rfl

/-- The right marked map is the literal inclusion, derived from the public square. -/
theorem standardAmalgam_right_eq_inclusion :
    d.standardAmalgam.right = inclusion (d.tits.B_le_standardParabolic {d.simple 1}) := by
  ext b
  obtain ⟨c, rfl⟩ := d.markedIso.middle.surjective b
  change (d.standardAmalgam.right (d.markedIso.middle c) : X ⧸ d.D) =
    (d.markedIso.middle c : X ⧸ d.D)
  rw [← d.markedIso.right_commutes, d.markedIso_right_apply, d.markedIso_middle_apply]
  rfl

/-- Transport the left index through the entire marked amalgam square. -/
theorem marked_amalgam_left_index {L C R : Type*} [Group L] [Group C] [Group R]
    {α : RankTwoAmalgam L C R} (e : RankTwoAmalgam.Iso α d.standardAmalgam) :
    α.left.range.index =
      (d.tits.B.subgroupOf (d.tits.standardParabolic {d.simple 0})).index := by
  have he : e.left.toMonoidHom.comp α.left =
      d.standardAmalgam.left.comp e.middle.toMonoidHom := by
    ext x
    exact congrArg Subtype.val (e.left_commutes x)
  have hr : α.left.range.map e.left.toMonoidHom = d.standardAmalgam.left.range := by
    rw [← MonoidHom.range_comp, he, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ e.middle.surjective, ← MonoidHom.range_eq_map]
  have hi := (index_map_of_bijective (f := e.left.toMonoidHom) e.left.bijective α.left.range).symm
  rw [hr] at hi
  simpa only [standardAmalgam_left_eq_inclusion, inclusion_range] using hi

/-- Transport the right index through the entire marked amalgam square. -/
theorem marked_amalgam_right_index {L C R : Type*} [Group L] [Group C] [Group R]
    {α : RankTwoAmalgam L C R} (e : RankTwoAmalgam.Iso α d.standardAmalgam) :
    α.right.range.index =
      (d.tits.B.subgroupOf (d.tits.standardParabolic {d.simple 1})).index := by
  have he : e.right.toMonoidHom.comp α.right =
      d.standardAmalgam.right.comp e.middle.toMonoidHom := by
    ext x
    exact congrArg Subtype.val (e.right_commutes x)
  have hr : α.right.range.map e.right.toMonoidHom = d.standardAmalgam.right.range := by
    rw [← MonoidHom.range_comp, he, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ e.middle.surjective, ← MonoidHom.range_eq_map]
  have hi := (index_map_of_bijective (f := e.right.toMonoidHom) e.right.bijective α.right.range).symm
  rw [hr] at hi
  simpa only [standardAmalgam_right_eq_inclusion, inclusion_range] using hi


/-- Both original endpoint indices with the same specified U and simple markings. -/
theorem marked_amalgam_indices (split : SplitData d.tits)
    {L C R : Type*} [Group L] [Group C] [Group R]
    {α : RankTwoAmalgam L C R} (e : RankTwoAmalgam.Iso α d.standardAmalgam) :
    α.left.range.index = 1 +
      ((split.U ⊓ unipotentConjugate split (d.simple 0)).subgroupOf split.U).index ∧
    α.right.range.index = 1 +
      ((split.U ⊓ unipotentConjugate split (d.simple 1)).subgroupOf split.U).index := by
  constructor
  · rw [marked_amalgam_left_index d e]
    exact singleton_parabolic_index split (d.simple_mem 0)
      (representative (d.simple 0)) (representative_spec (d.simple 0))
  · rw [marked_amalgam_right_index d e]
    exact singleton_parabolic_index split (d.simple_mem 1)
      (representative (d.simple 1)) (representative_spec (d.simple 1))

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
