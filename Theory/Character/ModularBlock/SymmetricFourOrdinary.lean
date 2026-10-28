module

public import Theory.Character.ModularBlock.SymmetricFourCartanData
public import Theory.Character.SymmetricFour

/-!
# All ordinary S₄ characters lie in its principal two-block

The explicit integral representations afford the complete ordinary table.
For each conjugacy class their central-character values differ from the
principal values by even integers. Reduction at any chosen prime above two
therefore places every character in the principal congruence block. Reindexing
the prescribed complete family gives the ordinary input to the Cartan assembly.

Source: Fong, *Some Sylow subgroups of order 32*, J. Algebra 6 (1967), p. 71;
the ordinary character and central-character calculations are proved here.
-/

public section
noncomputable section

namespace ModularBlock.SymmetricFourCartan

open PrincipalBlockConstruction BlockPreliminaries
open SymmetricFourClasses SymmetricFourCharacters

/-- Integral central-character values in the same row and class order as the table. -/
@[expose] def ordinaryCentralTable : Fin 5 → Fin 5 → ℤ :=
  ![![1, 6, 3, 8, 6], ![1, -6, 3, 8, -6], ![1, 0, 3, -4, 0],
    ![1, 2, -1, 0, -2], ![1, -2, -1, 0, 2]]

private theorem table_degree : ∀ i, table i 0 = (degree i : ℤ) := by decide +kernel
private theorem degree_pos : ∀ i, 0 < degree i := by decide +kernel
private theorem central_table_check : ∀ i j,
    (classSize j : ℤ) * table i j = ordinaryCentralTable i j * (degree i : ℤ) := by
  decide +kernel

/-- The class-sum scalar is computed from the actual irreducible character. -/
theorem ordinaryCentralCharacterValue_character (i : Fin 5) (g : Group) :
    ordinaryCentralCharacterValue (character i) (ConjClasses.mk g) =
      (ordinaryCentralTable i (classIndex g) : ℂ) := by
  rw [ordinaryCentralCharacterValue, card_carrier, character_apply, character_apply]
  change (classSize (classIndex g) : ℂ) * (table i (classIndex g) : ℂ) /
    (table i 0 : ℂ) = _
  rw [table_degree, Int.cast_natCast]
  apply (div_eq_iff (by exact_mod_cast (degree_pos i).ne')).mpr
  exact_mod_cast central_table_check i (classIndex g)

private theorem character_zero : character 0 = ordinaryPrincipalCharacter Group := by
  ext c
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
  rw [character_apply, ordinaryPrincipalCharacter_apply]
  generalize classIndex g = j
  fin_cases j <;> norm_num [table]

private theorem central_difference_even (i j : Fin 5) :
    ∃ n : ℤ, ordinaryCentralTable i j - ordinaryCentralTable 0 j = 2 * n := by
  refine ⟨(ordinaryCentralTable i j - ordinaryCentralTable 0 j) / 2, ?_⟩
  fin_cases i <;> fin_cases j <;> norm_num [ordinaryCentralTable]

/-- Every constructed irreducible is congruent to the principal character at
any prime of the cyclotomic order above two. -/
theorem character_sameTwoBlock (d : PrincipalCongruenceBlockData Group) (i : Fin 5) :
    SameTwoBlock d.eta_spec d.primeIdeal (character i) (character 0)
      (character_irreducible i) (character_irreducible 0) := by
  apply (sameTwoBlock_iff _ _ _ _ _ _).mpr
  intro c
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep c
  obtain ⟨n, hn⟩ := central_difference_even i (classIndex g)
  have heq : centralCharacterInCyclotomicOrder d.eta_spec (character i)
        (character_irreducible i) (ConjClasses.mk g) -
      centralCharacterInCyclotomicOrder d.eta_spec (character 0)
        (character_irreducible 0) (ConjClasses.mk g) =
      2 * (n : cyclotomicOrder d.eta) := by
    apply Subtype.ext
    change ordinaryCentralCharacterValue (character i) (ConjClasses.mk g) -
      ordinaryCentralCharacterValue (character 0) (ConjClasses.mk g) = (2 : ℂ) * (n : ℂ)
    rw [ordinaryCentralCharacterValue_character, ordinaryCentralCharacterValue_character]
    exact_mod_cast hn
  rw [heq, mul_comm]
  exact d.primeIdeal.mul_mem_left _ (two_mem_of_liesOver _ d.primeIdeal_liesOverTwo)

/-- The principal congruence block of S₄ contains every ordinary irreducible. -/
theorem ordinary_block_eq_univ (d : PrincipalCongruenceBlockData Group) :
    d.block = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro k
  obtain ⟨i, rfl⟩ := (familyIndex d.complete).surjective k
  rw [d.mem_block_iff]
  have hi := familyIndex_apply d.complete i
  have hzero : d.chi d.principal = character 0 := d.principal_eq.trans character_zero.symm
  simpa only [hi, hzero] using character_sameTwoBlock d i

/-- Reindex the actual character table into the prescribed ordinary block data. -/
def ordinaryCharacterData (d : PrincipalCongruenceBlockData Group) : OrdinaryCharacterData d where
  index := familyIndex d.complete
  block_eq_univ := ordinary_block_eq_univ d
  value i g hg := by
    rw [familyIndex_apply d.complete i]
    rcases SymmetricFourConjugacy.eq_one_or_isConj_threeCycle g hg with rfl | hc
    · rw [character_apply]
      change (table i 0 : ℂ) = _
      rw [table_degree, Int.cast_natCast]
      simp only [ite_true]
      rfl
    · have hgne : g ≠ 1 := by
        intro he
        rw [he] at hc
        exact SymmetricFourConjugacy.threeCycle_ne_one (isConj_one_right.mp hc.symm)
      rw [if_neg hgne, ← ConjClasses.mk_eq_mk_iff_isConj.mpr hc, character_apply]
      change (table i 3 : ℂ) = ordinaryThreeValue i
      fin_cases i
      · change ((1 : ℤ) : ℂ) = 1
        norm_num
      · change ((1 : ℤ) : ℂ) = 1
        norm_num
      · change ((-1 : ℤ) : ℂ) = -1
        norm_num
      · change ((0 : ℤ) : ℂ) = 0
        norm_num
      · change ((0 : ℤ) : ℂ) = 0
        norm_num

/-- Unconditional ordinary-character input for the characteristic-two S₄ Cartan calculation. -/
theorem nonempty_ordinaryCharacterData (d : PrincipalCongruenceBlockData Group) :
    Nonempty (OrdinaryCharacterData d) := ⟨ordinaryCharacterData d⟩

end ModularBlock.SymmetricFourCartan
