module

public import Theory.Character.PrimeOrderRationalValues
public import Theory.Character.ModularBlock.CyclicThirteenStructure
public import Theory.Character.ModularBlock.PrimeOrderSelfCentralizing
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.Linarith

/-!
# The principal cyclic thirteen-block with rational degrees 27 and 12

For a self-centralizing Sylow subgroup of order thirteen with automizer order
three, the principal block has seven rows. If rational irreducible characters
of degrees 27 and 12 are given, they are precisely the two nonprincipal
nonexceptional rows, and the four exceptional rows have degree 16.

First, each nonidentity Sylow element generates that subgroup, so its
centralizer has order thirteen. The column bound and the degree congruence
force the two rational character values to be 1 and -1. Prime-to-thirteen
degrees put both rows in the principal block. The cyclic-block rational-row
criterion identifies their positions, and the signed degree equation reads
1 + 27 - 12 ± E = 0. Positivity forces E = 16. A final permutation puts the
rows in the order principal, degree 27, degree 12, then the exceptional rows.

Simplicity is not needed. The original rational-value computations also need
no automizer hypothesis.

Source: Alperin--Brauer--Gorenstein, III.8 Proposition 5, printed p.117;
`refs/original/n-group-global/semidihedral-source/abg-iii7-8.txt`.
-/

noncomputable section
namespace CyclicThirteenBlock
variable {G : Type*} [Group G] [Finite G]

private theorem centralizer_eq_of_prime_card {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : Nat.card P = p)
    (hC : Subgroup.centralizer (P : Set G) = P)
    (u : P) (hu : u ≠ 1) : Subgroup.centralizer ({(u : G)} : Set G) = P := by
  have hpw : u ^ p = 1 := by simpa only [hP] using (pow_card_eq_one' (x := u))
  have ho : orderOf (u : G) = p := by
    exact (Subgroup.orderOf_coe u).trans (orderOf_eq_prime hpw hu)
  have hz : Subgroup.zpowers (u : G) = P :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr u.property)
      (by rw [Nat.card_zpowers, ho]; exact hP.le)
  calc
    Subgroup.centralizer ({(u : G)} : Set G) =
        Subgroup.centralizer (Subgroup.zpowers (u : G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    _ = Subgroup.centralizer (P : Set G) := by rw [hz]
    _ = P := hC

private theorem value_data {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) {n : ℕ}
    (hd : χ (ConjClasses.mk 1) = (n : ℂ))
    (P : Sylow 13 G) (hP : Nat.card P = 13)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (u : P) (hu : u ≠ 1)
    (hrat : ∃ q : ℚ, χ (ConjClasses.mk (u : G)) = (q : ℂ)) :
    ∃ z : ℤ, χ (ConjClasses.mk (u : G)) = (z : ℂ) ∧
      13 ∣ z - n ∧ -3 ≤ z ∧ z ≤ 3 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hcard : Nat.card ↥P = 13 := hP
  have hpw : u ^ 13 = 1 := by simpa only [hcard] using (pow_card_eq_one' (x := u))
  have hpwG : (u : G) ^ 13 = 1 := by exact_mod_cast hpw
  obtain ⟨z, hz, hmod, hbound⟩ :=
    PrimeOrderRationalValues.integer_value_congruence_bound hχ (by decide) hd (u : G) hpwG hrat
  rw [centralizer_eq_of_prime_card (P : Subgroup G) hP hC u hu,
    hP] at hbound
  norm_num at hbound
  have hb : -4 < z ∧ z < 4 := by
    constructor <;> nlinarith [sq_nonneg (z + 4), sq_nonneg (z - 4)]
  exact ⟨z, hz, hmod, by omega, by omega⟩

/-- The rational degree-27 row takes value one on nonidentity elements of
a self-centralizing Sylow subgroup of order 13. -/
public theorem degree_twenty_seven_value {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ)
    (hd : χ (ConjClasses.mk 1) = 27)
    (P : Sylow 13 G) (hP : Nat.card P = 13)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (u : P) (hu : u ≠ 1)
    (hrat : ∃ q : ℚ, χ (ConjClasses.mk (u : G)) = (q : ℂ)) :
    χ (ConjClasses.mk (u : G)) = 1 := by
  obtain ⟨z, hz, hmod, hlo, hhi⟩ := value_data hχ (n := 27) hd P hP hC u hu hrat
  have hz1 : z = 1 := by omega
  simpa [hz1] using hz

/-- The rational degree-12 row takes value minus one on nonidentity elements
of a self-centralizing Sylow subgroup of order 13. -/
public theorem degree_twelve_value {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ)
    (hd : χ (ConjClasses.mk 1) = 12)
    (P : Sylow 13 G) (hP : Nat.card P = 13)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (u : P) (hu : u ≠ 1)
    (hrat : ∃ q : ℚ, χ (ConjClasses.mk (u : G)) = (q : ℂ)) :
    χ (ConjClasses.mk (u : G)) = -1 := by
  obtain ⟨z, hz, hmod, hlo, hhi⟩ := value_data hχ (n := 12) hd P hP hC u hu hrat
  have hz1 : z = -1 := by omega
  simpa [hz1] using hz

open ModularBlock.PrimeBlockConstruction
open ModularBlock.CyclicThirteen

private theorem normalized_rows
    (d : PrimeCongruenceBlockData 13 G) (P : Sylow 13 G)
    (s : BlockStructure d P) {α β : ConjClassFunction G}
    (a b : Fin 3)
    (ha : d.chi (s.rows (a.castAdd 4)).val = α)
    (hb : d.chi (s.rows (b.castAdd 4)).val = β)
    (hα : α (ConjClasses.mk 1) = 27)
    (hβ : β (ConjClasses.mk 1) = 12)
    (hsa : s.sign a = 1) (hsb : s.sign b = -1) :
    ∃ row : Fin 7 ≃ {i : d.I // i ∈ d.block},
      (row 0).val = d.principal ∧ d.chi (row 1).val = α ∧
      d.chi (row 2).val = β ∧
      ∀ j, d.chi (row j).val (ConjClasses.mk 1) =
        (![1, 27, 12, 16, 16, 16, 16] : Fin 7 → ℂ) j := by
  have hN0 : s.degree 0 = 1 := by
    have h := s.degree_value 0
    change d.chi (s.rows 0).val (ConjClasses.mk 1) = _ at h
    rw [s.principal_row, d.principal_eq] at h
    norm_num [ModularBlock.PrincipalBlockConstruction.ordinaryPrincipalCharacter] at h
    exact_mod_cast h.symm
  have hNa : s.degree a = 27 := by
    have h := s.degree_value a
    rw [ha, hα] at h
    exact_mod_cast h.symm
  have hNb : s.degree b = 12 := by
    have h := s.degree_value b
    rw [hb, hβ] at h
    exact_mod_cast h.symm
  have ha0 : a ≠ 0 := by intro h; rw [h, hN0] at hNa; contradiction
  have hb0 : b ≠ 0 := by intro h; rw [h, hN0] at hNb; contradiction
  have hab : a ≠ b := by intro h; rw [h, hNb] at hNa; contradiction
  have hab_cases : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
    fin_cases a <;> fin_cases b <;> simp_all
  have hE : s.exceptionalDegree = 16 := by
    have heq := s.degree_equation
    have hepos := s.exceptionalDegree_pos
    have hesign := s.exceptionalSign_unit
    rcases hab_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [Fin.sum_univ_three, s.sign_zero, hN0, hNa, hNb, hsa, hsb] at heq <;>
      rcases hesign with hesign | hesign <;> rw [hesign] at heq <;> norm_num at heq <;> omega
  rcases hab_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · change d.chi (s.rows 1).val = α at ha
    change d.chi (s.rows 2).val = β at hb
    refine ⟨s.rows, s.principal_row, ha, hb, ?_⟩
    intro j
    fin_cases j
    · simp [s.principal_row, d.principal_eq,
        ModularBlock.PrincipalBlockConstruction.ordinaryPrincipalCharacter]
    · simpa [ha] using hα
    · simpa [hb] using hβ
    · simpa [hE, Equiv.swap_apply_def] using s.exceptional_degree 0
    · simpa [hE, Equiv.swap_apply_def] using s.exceptional_degree 1
    · simpa [hE, Equiv.swap_apply_def] using s.exceptional_degree 2
    · simpa [hE, Equiv.swap_apply_def] using s.exceptional_degree 3
  · change d.chi (s.rows 2).val = α at ha
    change d.chi (s.rows 1).val = β at hb
    refine ⟨(Equiv.swap (1 : Fin 7) 2).trans s.rows, ?_, ?_, ?_, ?_⟩
    · simpa [Equiv.swap_apply_def] using s.principal_row
    · simpa using ha
    · simpa using hb
    · intro j
      fin_cases j
      · simp [Equiv.swap_apply_def, s.principal_row, d.principal_eq,
          ModularBlock.PrincipalBlockConstruction.ordinaryPrincipalCharacter]
      · simpa [ha] using hα
      · simpa [hb] using hβ
      · simpa [hE, Equiv.swap_apply_def] using s.exceptional_degree 0
      · simpa [hE, Equiv.swap_apply_def] using s.exceptional_degree 1
      · simpa [hE, Equiv.swap_apply_def] using s.exceptional_degree 2
      · simpa [hE, Equiv.swap_apply_def] using s.exceptional_degree 3

/-- A block containing a row of degree prime to thirteen is principal.
Since the Sylow subgroup has order thirteen, and the principal character has
degree one, this is the degree formulation of uniqueness of positive defect. -/
public theorem blockOf_eq_principal_of_prime_to_degree
    (P : Sylow 13 G) (hP : Nat.card P = 13)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (d : PrimeCongruenceBlockData 13 G) (i : d.I) (n : ℕ)
    (hn : d.chi i (ConjClasses.mk 1) = (n : ℂ)) (hp : ¬ 13 ∣ n) :
    d.blockOf i = d.block := by
  have hm := mem_block_of_prime_to_degree P hP hC d i n hn hp
  have heq := (d.mem_blockOf_iff i d.principal).mp hm
  ext j
  change j ∈ d.blockOf i ↔ j ∈ d.blockOf d.principal
  simp only [PrimeCongruenceBlockData.mem_blockOf_iff,
    PrimeCongruenceBlockData.SameBlock] at heq ⊢
  rw [heq]

/-- The principal thirteen-block consists of the principal row, the rational
rows of degrees 27 and 12, and four rows of degree 16. The two specified
rational rows have values 1 and -1 on the punctured Sylow subgroup.
Simplicity is unnecessary for this character-theoretic conclusion. -/
public theorem exists_rows
    (P : Sylow 13 G) (hP : Nat.card P = 13)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (hindex : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 3)
    {α β : ConjClassFunction G}
    (hα : IsIrreducibleConjCharacter α) (hβ : IsIrreducibleConjCharacter β)
    (hαrat : ∀ g : G, ∃ q : ℚ, α (ConjClasses.mk g) = (q : ℂ))
    (hβrat : ∀ g : G, ∃ q : ℚ, β (ConjClasses.mk g) = (q : ℂ))
    (hαdeg : α (ConjClasses.mk 1) = 27) (hβdeg : β (ConjClasses.mk 1) = 12)
    (d : PrimeCongruenceBlockData 13 G) :
    ∃ row : Fin 7 ≃ {i : d.I // i ∈ d.block},
      d.chi (row 0).val = ModularBlock.PrincipalBlockConstruction.ordinaryPrincipalCharacter G ∧
      d.chi (row 1).val = α ∧ d.chi (row 2).val = β ∧
      (∀ j, d.chi (row j).val (ConjClasses.mk 1) =
        (![1, 27, 12, 16, 16, 16, 16] : Fin 7 → ℂ) j) ∧
      ∀ u : P, u ≠ 1 → α (ConjClasses.mk (u : G)) = 1 ∧
        β (ConjClasses.mk (u : G)) = -1 := by
  obtain ⟨s⟩ := nonempty_blockStructure d P hP hC hindex
  obtain ⟨i, hi⟩ := d.complete.2.1 α hα
  obtain ⟨k, hk⟩ := d.complete.2.1 β hβ
  have him : i ∈ d.block := mem_block_of_prime_to_degree P hP hC d i 27
    (by simpa [hi] using hαdeg) (by decide)
  have hkm : k ∈ d.block := mem_block_of_prime_to_degree P hP hC d k 12
    (by simpa [hk] using hβdeg) (by decide)
  obtain ⟨a, ha⟩ := s.rational_row i him (by simpa [hi] using hαrat)
  obtain ⟨b, hb⟩ := s.rational_row k hkm (by simpa [hk] using hβrat)
  have hva (u : P) (hu : u ≠ 1) : α (ConjClasses.mk (u : G)) = 1 :=
    degree_twenty_seven_value hα hαdeg P hP hC u hu (hαrat u)
  have hvb (u : P) (hu : u ≠ 1) : β (ConjClasses.mk (u : G)) = -1 :=
    degree_twelve_value hβ hβdeg P hP hC u hu (hβrat u)
  have hsa : s.sign a = 1 := by
    have h := s.nonexceptional_value a s.generator s.generator_ne_one
    rw [ha, hi, hva s.generator s.generator_ne_one] at h
    exact_mod_cast h.symm
  have hsb : s.sign b = -1 := by
    have h := s.nonexceptional_value b s.generator s.generator_ne_one
    rw [hb, hk, hvb s.generator s.generator_ne_one] at h
    exact_mod_cast h.symm
  obtain ⟨row, hr0, hr1, hr2, hrdeg⟩ := normalized_rows d P s a b
    (by rw [ha, hi]) (by rw [hb, hk]) hαdeg hβdeg hsa hsb
  exact ⟨row, by rw [hr0, d.principal_eq], hr1, hr2, hrdeg,
    fun u hu => ⟨hva u hu, hvb u hu⟩⟩

end CyclicThirteenBlock
