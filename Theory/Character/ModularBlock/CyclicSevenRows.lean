module

public import Theory.Character.ModularBlock.CyclicSevenOrdinaryData
public import Theory.Character.ModularBlock.SevenSelfCentralizing
public import Theory.Character.ModularBlock.PrimePowerDegree
public import Theory.Character.DefectZeroVanishing
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Identifying the ordinary seven-rows with the principal block

Nonzero values at a nonidentity element of the order-seven Sylow subgroup
force degree prime to seven, by defect-zero vanishing. Conversely a row
vanishing on the punctured Sylow subgroup cannot be in the principal block:
central-character congruences and averaging would make the principal degree
divisible by seven.

Consequently ordinary spectral rows, together with principal-block membership
for degrees prime to seven, give the required block equivalence. The membership
theorem follows from self-centralization. Ordinary-row existence is a separate
input: this module does not import its construction.

Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from `CyclicThirteenRows`, whose sources are Brauer--Tuan (1945),
§2 and Lemma 2, and Alperin--Brauer--Gorenstein III.8 Proposition 5, pp.116--117.
-/

public section
noncomputable section
namespace ModularBlock.CyclicSeven
open PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]

private theorem ofConj_irreducible {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) :
    IsIrreducibleCharacter (ofConjClassFunction χ) := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using hχ.2
  · rw [hρ]
    rfl

/-- A principal-block row cannot vanish on the punctured Sylow subgroup. -/
theorem exists_value_ne_zero_of_mem_block (d : PrimeCongruenceBlockData 7 G)
    (P : Sylow 7 G) (hP : Nat.card P = 7) (i : d.I) (hi : i ∈ d.block) :
    ∃ u : P, u ≠ 1 ∧ d.chi i (ConjClasses.mk (u : G)) ≠ 0 := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  let : CommGroup P := IsCyclic.commGroup
  by_contra h
  have hv : ∀ u : P, u ≠ 1 → d.chi i (ConjClasses.mk (u : G)) = 0 := by
    simpa only [not_exists, not_and, not_not] using h
  have hclass (u : P) : ¬ 7 ∣ Nat.card (ConjClasses.mk (u : G)).carrier := by
    have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
      intro x hx
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : P) u)
    rw [ConjClasses.nat_card_carrier_eq_index_centralizer]
    exact fun h => P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hle))
  have hprincipal : d.principal ∈ d.blockOf i := by
    rw [d.mem_blockOf_iff]
    exact ((d.mem_blockOf_iff i d.principal).mp hi).symm
  obtain ⟨n, hn, hdiv⟩ := d.degree_dvd_of_subgroup_vanishing i (P : Subgroup G)
    (by rw [hP]) (fun u _ => hclass u) hv d.principal hprincipal
  have hn1 : n = 1 := by
    have hc : (1 : ℂ) = (n : ℂ) := by simpa [d.principal_eq] using hn
    exact_mod_cast hc.symm
  subst n
  norm_num at hdiv

/-- Nonvanishing in an order-seven Sylow subgroup excludes defect zero. -/
theorem degree_prime_to_seven_of_value_ne_zero
    (d : PrimeCongruenceBlockData 7 G) (P : Sylow 7 G) (hP : Nat.card P = 7)
    (i : d.I) (n : ℕ) (hn : d.chi i (ConjClasses.mk 1) = (n : ℂ))
    (u : P) (hu : u ≠ 1) (hv : d.chi i (ConjClasses.mk (u : G)) ≠ 0) :
    ¬ 7 ∣ n := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hord : orderOf u = 7 := by
    have hcard : Nat.card ↥P = 7 := hP
    have hdiv : orderOf u ∣ 7 := by simpa only [hcard] using orderOf_dvd_natCard u
    exact ((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hdiv).resolve_left
      (fun h => hu (orderOf_eq_one_iff.mp h))
  intro hdiv
  apply hv
  exact OrdinaryCharacter.value_eq_zero_of_sylow_card_dvd_degree P
    (ofConj_irreducible (d.complete.1 i)) hn (by simpa only [hP] using hdiv) (u : G)
    (by rw [Subgroup.orderOf_coe, hord])

/-- The five ordinary rows are exactly the principal-block rows. Nonvanishing
gives prime-to-seven degree and hence membership by self-centralization;
vanishing of all other rows and principal-block nonvanishing give surjectivity. -/
def OrdinaryRows.toSpectralRows {d : PrimeCongruenceBlockData 7 G} {P : Sylow 7 G}
    (s : OrdinaryRows d P) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G)) : SpectralRows d P := by
  classical
  have hrow (j : Fin 5) : s.rows j ∈ d.block := by
    obtain ⟨n, ρ, hρ⟩ := (d.complete.1 (s.rows j)).1
    have hn : d.chi (s.rows j) (ConjClasses.mk 1) = (n : ℂ) := by
      rw [hρ]
      change ρ.character 1 = (n : ℂ)
      simp
    exact mem_block_of_prime_to_seven_degree P hP hC d _ n hn (degree_prime_to_seven_of_value_ne_zero d P hP _ n hn
      s.generator s.generator_ne_one (s.value_ne_zero j))
  let f : Fin 5 → {i : d.I // i ∈ d.block} := fun j => ⟨s.rows j, hrow j⟩
  have hf : Function.Bijective f := by
    refine ⟨fun j k h => s.rows.injective (congrArg Subtype.val h), ?_⟩
    intro i
    have hirange : i.val ∈ Set.range s.rows := by
      by_contra h
      obtain ⟨u, hu, hv⟩ := exists_value_ne_zero_of_mem_block d P hP i.val i.property
      exact hv (s.off_rows_vanish i.val h u hu)
    obtain ⟨j, hj⟩ := hirange
    exact ⟨j, Subtype.ext hj⟩
  exact {
    rows := Equiv.ofBijective f hf
    principal_row := s.principal_row
    sign := s.sign
    sign_unit := s.sign_unit
    sign_zero := s.sign_zero
    nonexceptional_value := s.nonexceptional_value
    exceptionalDegree := s.exceptionalDegree
    exceptional_degree := s.exceptional_degree
    exceptionalSign := s.exceptionalSign
    exceptionalSign_unit := s.exceptionalSign_unit
    generator := s.generator
    generator_ne_one := s.generator_ne_one
    root := s.root
    root_primitive := s.root_primitive
    periods := s.periods
    exceptional_value := s.exceptional_value }

end ModularBlock.CyclicSeven
