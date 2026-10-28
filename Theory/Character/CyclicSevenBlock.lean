module

public import Theory.Character.CyclicSevenValues
public import Theory.Character.ModularBlock.CyclicSevenStructure

/-!
# The degree calculation in the cyclic seven-block

Given the actual block structure, a rational row of degree 27 is the second
nonexceptional row. Its value is minus one, so the signed degree equation
forces all three exceptional degrees to be 26. Construction of the block
structure and membership of the specified row are separate prerequisites.

Source: Fong (1967), printed p.75, citing Brauer (1942).
-/

public section
noncomputable section
namespace CyclicSevenBlock
open ModularBlock.PrimeBlockConstruction ModularBlock.CyclicSeven
variable {G : Type*} [Group G] [Finite G]

/-- Identify the rational degree-27 row and compute all exceptional degrees
once the actual principal-block structure and row membership are supplied. -/
theorem rows_of_blockStructure
    {d : PrimeCongruenceBlockData 7 G} {P : Sylow 7 G}
    (s : BlockStructure d P) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (i : d.I) (hi : i ∈ d.block)
    (hrat : ∀ g : G, ∃ q : ℚ, d.chi i (ConjClasses.mk g) = (q : ℂ))
    (hdeg : d.chi i (ConjClasses.mk 1) = 27) :
    (s.rows 1).val = i ∧ s.exceptionalDegree = 26 ∧
      (∀ j, d.chi (s.rows j).val (ConjClasses.mk 1) =
        (![1, 27, 26, 26, 26] : Fin 5 → ℂ) j) := by
  obtain ⟨a, ha⟩ := s.rational_row i hi hrat
  have hN0 : s.degree 0 = 1 := by
    have h := s.degree_value 0
    change d.chi (s.rows 0).val (ConjClasses.mk 1) = _ at h
    rw [s.principal_row, d.principal_eq] at h
    norm_num [ModularBlock.PrincipalBlockConstruction.ordinaryPrincipalCharacter] at h
    exact_mod_cast h.symm
  have hNa : s.degree a = 27 := by
    have h := s.degree_value a
    rw [ha, hdeg] at h
    exact_mod_cast h.symm
  have ha0 : a ≠ 0 := by intro h; rw [h, hN0] at hNa; contradiction
  have ha1 : a = 1 := by fin_cases a <;> simp_all
  subst a
  have hs1 : s.sign 1 = -1 := by
    have h := s.nonexceptional_value 1 s.generator s.generator_ne_one
    rw [ha, degree_twenty_seven_value (d.complete.1 i) hdeg P hP hC
      s.generator s.generator_ne_one (hrat s.generator)] at h
    exact_mod_cast h.symm
  have hE : s.exceptionalDegree = 26 := by
    have heq := s.degree_equation
    have hepos := s.exceptionalDegree_pos
    simp only [Fin.sum_univ_two, s.sign_zero, hN0, hNa, hs1] at heq
    rcases s.exceptionalSign_unit with h | h <;> rw [h] at heq <;>
      norm_num at heq <;> omega
  change (s.rows 1).val = i at ha
  refine ⟨ha, hE, ?_⟩
  intro j
  fin_cases j
  · simp [s.principal_row, d.principal_eq,
      ModularBlock.PrincipalBlockConstruction.ordinaryPrincipalCharacter]
  · simpa [ha] using hdeg
  · simpa [hE] using s.exceptional_degree 0
  · simpa [hE] using s.exceptional_degree 1
  · simpa [hE] using s.exceptional_degree 2

/-- In particular the exceptional degree 26 is the degree of an actual
irreducible character, rather than just a formal row in numerical data. -/
theorem exists_degree_twenty_six_of_blockStructure
    {d : PrimeCongruenceBlockData 7 G} {P : Sylow 7 G}
    (s : BlockStructure d P) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (i : d.I) (hi : i ∈ d.block)
    (hrat : ∀ g : G, ∃ q : ℚ, d.chi i (ConjClasses.mk g) = (q : ℂ))
    (hdeg : d.chi i (ConjClasses.mk 1) = 27) :
    ∃ ψ : ClassFunction G, IsIrreducibleCharacter ψ ∧ ψ 1 = 26 := by
  have hE := (rows_of_blockStructure s hP hC i hi hrat hdeg).2.1
  let j := (s.rows ((0 : Fin 3).natAdd 2)).val
  have hj := d.complete.1 j
  obtain ⟨n, ρ, hρ⟩ := hj.1
  refine ⟨ofConjClassFunction (d.chi j), ?_, ?_⟩
  · refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
    · simpa [hρ] using hj.2
    · rw [hρ]; rfl
  · change d.chi j (ConjClasses.mk 1) = 26
    simpa only [hE, Nat.cast_ofNat] using s.exceptional_degree 0

end CyclicSevenBlock
