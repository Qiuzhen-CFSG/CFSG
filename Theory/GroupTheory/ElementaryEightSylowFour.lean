module
public import Theory.GroupTheory.ElementaryEightSolvableCore
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.Nilpotent

/-!
# Elementary-eight automizers with Sylow two-order four

A subgroup of `Aut(C₂³)` with Sylow two-subgroups of order four has order
four or twelve. The other divisors of 168 with two-part four are 28 and 84;
Sylow counting would give a normal seven-subgroup, contradicting the odd
order of its ambient normalizer. The action on the at most three cosets of
a Sylow two-subgroup proves solvability. The elementary-eight Fitting
calculation then identifies that Sylow subgroup with the two-core.

This removes an ambient solvability assumption from the small automizer
step used in MacWilliams's involution-fusion argument, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3. The proof uses only Sylow counting,
the order-168 automorphism calculation, and solvability of the symmetric
group on four letters.
-/

open Subgroup

private theorem small_candidates
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G ∣ 168) (P : Sylow 2 G) (hP : Nat.card P = 4) :
    Nat.card G = 4 ∨ Nat.card G = 12 ∨ Nat.card G = 28 ∨ Nat.card G = 84 := by
  have hfour : 4 ∣ Nat.card G := hP ▸ P.toSubgroup.card_subgroup_dvd_card
  have hnot : ¬ 8 ∣ Nat.card G := by
    intro h
    have hh := P.pow_dvd_card_of_pow_dvd_card (n := 3) h
    norm_num [hP] at hh
  have hmem := Nat.mem_divisors.mpr ⟨hcard, by decide⟩
  have hd : (168 : ℕ).divisors =
      {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by decide
  rw [hd] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

private theorem normal_seven
    {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 28 ∨ Nat.card G = 84) (P : Sylow 7 G) :
    Nat.card P = 7 ∧ P.toSubgroup.Normal := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hP : Nat.card P = 7 := by
    rw [P.card_eq_multiplicity]
    rcases hcard with h | h
    · rw [h, show (28 : ℕ) = 4 * 7 by decide,
        Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 4)]
      norm_num [(show Nat.Prime 7 by decide).factorization]
    · rw [h, show (84 : ℕ) = 12 * 7 by decide,
        Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 12)]
      norm_num [(show Nat.Prime 7 by decide).factorization]
  refine ⟨hP, ?_⟩
  have hi := P.toSubgroup.card_mul_index
  rw [hP] at hi
  have hd : Nat.card (Sylow 7 G) ∣ 12 := by
    rcases hcard with h | h
    · have he : P.toSubgroup.index = 4 := by omega
      exact (he ▸ P.card_dvd_index).trans (by decide)
    · have he : P.toSubgroup.index = 12 := by omega
      exact he ▸ P.card_dvd_index
  have hm := card_sylow_modEq_one 7 G
  change Nat.card (Sylow 7 G) % 7 = 1 % 7 at hm
  have hmem := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hd12 : (12 : ℕ).divisors = {1, 2, 3, 4, 6, 12} := by decide
  rw [hd12] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hc : Nat.card (Sylow 7 G) = 1 := by omega
  let : Subsingleton (Sylow 7 G) := (Nat.card_eq_one_iff_unique.mp hc).1
  exact P.normal_of_subsingleton

/-- An elementary-eight automizer with Sylow two-subgroups of order four
has order four or twelve. -/
public theorem card_eq_four_or_twelve_of_elementary_eight_automorphisms
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E))
    (P : Sylow 2 A) (hP : Nat.card P = 4) :
    Nat.card A = 4 ∨ Nat.card A = 12 := by
  have hd : Nat.card A ∣ 168 :=
    (card_mulAut_of_elementary_eight E hE) ▸ A.card_subgroup_dvd_card
  rcases small_candidates hd P hP with h | h | hlarge
  · exact Or.inl h
  · exact Or.inr h
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let Q : Sylow 7 A := Classical.choice inferInstance
  obtain ⟨hQ, hQn⟩ := normal_seven hlarge Q
  let : Q.toSubgroup.Normal := hQn
  let B := Q.toSubgroup.map A.subtype
  have hB : Nat.card B = 7 :=
    (card_map_of_injective A.subtype_injective).trans hQ
  have hAN : A ≤ normalizer (B : Set (MulAut E)) := by
    have hh := Q.toSubgroup.le_normalizer_map A.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, A.range_subtype] using hh
  have htwo : 2 ∣ Nat.card (normalizer (B : Set (MulAut E))) := by
    apply dvd_trans ?_ (card_dvd_of_le hAN)
    exact (by decide : 2 ∣ 4).trans (hP ▸ P.toSubgroup.card_subgroup_dvd_card)
  exact ((odd_card_normalizer_of_elementary_eight_seven E hE B hB).not_two_dvd_nat htwo).elim

private theorem solvable_of_small_index_two_group
    {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) (hP : IsPGroup 2 P) (hi : P.index ≤ 4) : Group.IsSolvable G := by
  classical
  let : Fintype (G ⧸ P) := Fintype.ofFinite _
  change Nat.card (G ⧸ P) ≤ 4 at hi
  have hc : Fintype.card (G ⧸ P) ≤ Fintype.card (Fin 4) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using hi
  let e : (G ⧸ P) ↪ Fin 4 := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (G ⧸ P)) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  let : Group.IsNilpotent P := hP.isNilpotent
  apply Group.isSolvable_of_ker_le_range P.subtype (MulAction.toPermHom G (G ⧸ P))
  rw [range_subtype, ← P.normalCore_eq_ker]
  exact P.normalCore_le

/-- No solvability hypothesis is needed when the Sylow two-order is four. -/
public theorem isSolvable_of_elementary_eight_automorphisms_sylow_four
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E))
    (P : Sylow 2 A) (hP : Nat.card P = 4) : Group.IsSolvable A := by
  have hc := card_eq_four_or_twelve_of_elementary_eight_automorphisms E hE A P hP
  have hi := P.toSubgroup.card_mul_index
  rw [hP] at hi
  exact solvable_of_small_index_two_group P.toSubgroup P.isPGroup' (by omega)

/-- The Sylow two-subgroup of such an automizer is its two-core. -/
public theorem sylow_eq_pCore_of_elementary_eight_automorphisms_sylow_four
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) (A : Subgroup (MulAut E))
    (P : Sylow 2 A) (hP : Nat.card P = 4) : (P : Subgroup A) = pCore 2 A := by
  let : Group.IsSolvable A :=
    isSolvable_of_elementary_eight_automorphisms_sylow_four E hE A P hP
  have hfour : 4 ∣ Nat.card A := hP ▸ P.toSubgroup.card_subgroup_dvd_card
  exact (eq_of_le_of_card_ge (pCore_isPGroup.le_sylow_of_normal P)
    (hP ▸ four_le_card_pCore_of_solvable_elementary_eight_automorphisms E hE A hfour)).symm
