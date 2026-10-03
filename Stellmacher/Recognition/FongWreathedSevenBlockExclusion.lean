module

public import Theory.Character.CyclicSevenBlock
public import Theory.Character.ModularBlock.CyclicSevenOrdinaryConstruction
public import Theory.Character.ModularBlock.CyclicSevenRows

/-!
# The degree obstruction in Fong's order-18144 case

The cyclic seven-block calculation gives three irreducibles of degree 26.
Since an irreducible degree divides the group order and 26 does not divide
18144, this excludes that order. The ordinary cyclic-seven rows are identified
with the principal block, whose projector gives the degree equation. A given
rational irreducible of degree 27 is then its second nonexceptional row.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed p.75, citing Brauer (1942).
-/

public section
namespace Stellmacher.Recognition.FongWreathed
open ModularBlock.PrimeBlockConstruction ModularBlock.CyclicSeven
variable {G : Type*} [Group G] [Finite G]

/-- Fong's degree-26 divisibility obstruction to order 18144. -/
theorem order_ne_18144_of_degree_twenty_six
    {ψ : ClassFunction G} (hψ : IsIrreducibleCharacter ψ) (hdeg : ψ 1 = 26) :
    Nat.card G ≠ 18144 := by
  have hd : hψ.degree = 26 := by exact_mod_cast hψ.degree_eq.symm.trans hdeg
  have hdiv := hψ.degree_dvd_card
  rw [hd] at hdiv
  intro hG
  rw [hG] at hdiv
  norm_num at hdiv

/-- The degree contradiction from an actual seven-block and a rational member
of degree 27. The theorem below constructs these block inputs from local data. -/
theorem order_ne_18144_of_seven_block
    {d : PrimeCongruenceBlockData 7 G} {P : Sylow 7 G}
    (s : BlockStructure d P) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (i : d.I) (hi : i ∈ d.block)
    (hrat : ∀ g : G, ∃ q : ℚ, d.chi i (ConjClasses.mk g) = (q : ℂ))
    (hdeg : d.chi i (ConjClasses.mk 1) = 27) : Nat.card G ≠ 18144 := by
  obtain ⟨ψ, hψ, hd⟩ := CyclicSevenBlock.exists_degree_twenty_six_of_blockStructure
    s hP hC i hi hrat hdeg
  exact order_ne_18144_of_degree_twenty_six hψ hd

/-- Fong's order-18144 exclusion from the local seven-subgroup data and an
actual rational irreducible character of degree 27. -/
theorem order_ne_18144_of_rational_degree_twenty_seven
    (P : Sylow 7 G) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (hindex : (P : Subgroup G).relIndex
      (Subgroup.normalizer (P : Set G)) = 2)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hrat : ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ))
    (hdeg : χ 1 = 27) : Nat.card G ≠ 18144 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨d⟩ := exists_primeCongruenceBlockData 7 G
  obtain ⟨n, ρ, hρ, hχeq⟩ := hχ
  have hclass : IsClassFunction χ := by
    rw [hχeq]
    exact ρ.char_conj
  have hθeq : toConjClassFunction χ hclass = characterClassFunction ρ := by
    apply toConjClassFunction_eq_of_apply
    intro g
    change ρ.character g = χ g
    exact (congrFun hχeq g).symm
  have hθ : IsIrreducibleConjCharacter (toConjClassFunction χ hclass) := by
    rw [hθeq]
    exact ⟨⟨n, ρ, rfl⟩, (irreducible_iff_character_norm_one ρ).mp hρ⟩
  obtain ⟨i, hi⟩ := d.complete.2.1 (toConjClassFunction χ hclass) hθ
  have hrat' : ∀ g : G, ∃ q : ℚ, d.chi i (ConjClasses.mk g) = (q : ℂ) := by
    intro g
    obtain ⟨q, hq⟩ := hrat g
    exact ⟨q, by rw [hi]; exact hq⟩
  have hdeg' : d.chi i (ConjClasses.mk 1) = 27 := by
    rw [hi]
    exact hdeg
  have hindex' : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 2 := by
    rw [hC]
    exact hindex
  obtain ⟨s⟩ := ModularBlock.CyclicSeven.nonempty_ordinaryRows d P hP hC hindex'
  let b := (s.toSpectralRows hP hC).blockStructure hP
  have hmem : i ∈ d.block := by
    apply mem_block_of_prime_to_seven_degree
      P hP hC d i 27 hdeg'
    norm_num
  exact order_ne_18144_of_seven_block b hP hC i hmem hrat' hdeg'

end Stellmacher.Recognition.FongWreathed
