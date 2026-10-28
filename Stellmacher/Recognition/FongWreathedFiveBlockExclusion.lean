module

public import Stellmacher.Recognition.FongWreathedOrderCandidates
public import Theory.Character.ModularBlock.FiveSelfCentralizing
public import Theory.Character.ModularBlock.CyclicFiveData
public import Theory.Character.ModularBlock.CyclicFiveStructure

/-!
# Fong's principal five-block obstruction

A centralizer of order five at ambient order 90720 gives a self-centralizing
Sylow five-subgroup. Sylow's congruence forces automizer order four. The
four rational characters in Fong's packet belong to its principal five-block,
since their degrees 1, 27, 21 and 7 are prime to five. In the full-automizer
cyclic-block rows all degrees are congruent to plus or minus one modulo five,
contradicting degree 27.

The membership, local reduction, construction of the actual five cyclic-block
rows, and final assembly are proved here.

Source: Fong, Some Sylow subgroups of order 32 and a characterization of
U(3,3), J. Algebra 6 (1967), printed pp.74–75, citing Brauer (1942).
-/

public section
noncomputable section
namespace Stellmacher.Recognition.FongWreathed
open ModularBlock PrincipalBlockConstruction PrimeBlockConstruction
open FongWreathedExceptional
variable {G : Type*} [Group G] [Finite G]

/-- At order 90720 the self-centralizing five-subgroup has full automizer.
This uses the actual Sylow congruence, and does not need simplicity. -/
theorem exists_five_sylow_full_automizer
    (hG : Nat.card G = 90720) {s : G} (hs : orderOf s = 5)
    (hC : Nat.card (Subgroup.centralizer ({s} : Set G)) = 5) :
    ∃ T : Sylow 5 G, Nat.card T = 5 ∧
      Subgroup.centralizer (T : Set G) = (T : Subgroup G) ∧
      (Subgroup.centralizer (T : Set G)).relIndex
        (Subgroup.normalizer (T : Set G)) = 4 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨T, hle⟩ := (IsPGroup.of_card (show Nat.card (Subgroup.zpowers s) = 5 ^ 1 by
    rw [Nat.card_zpowers, hs, pow_one])).exists_le_sylow
  have hT : Nat.card T = 5 := T.card_eq_prime_of_dvd_of_not_sq_dvd
    (by rw [hG]; norm_num) (by rw [hG]; norm_num)
  have hz : Subgroup.zpowers s = (T : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, hs, hT])
  have hzs : Subgroup.zpowers s = Subgroup.centralizer ({s} : Set G) :=
    Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
      (by rw [Nat.card_zpowers, hs, hC])
  have hCT : Subgroup.centralizer (T : Set G) = (T : Subgroup G) := by
    change Subgroup.centralizer ((T : Subgroup G) : Set G) = (T : Subgroup G)
    rw [← hz, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    simpa only [Subgroup.zpowers_eq_closure] using hzs.symm
  let k := (Subgroup.centralizer (T : Set G)).relIndex
    (Subgroup.normalizer (T : Set G))
  have hk : k ∣ 4 := T.centralizer_relIndex_normalizer_dvd_prime_sub_one hT
  have hkle : k ≤ 4 := Nat.le_of_dvd (by decide) hk
  have hcong := T.card_div_prime_modEq_of_normalizer_card
    (T.normalizer_card_of_self_centralizing hT hCT)
  change Nat.card G / 5 ≡ k [MOD 5] at hcong
  rw [hG] at hcong
  have hk4 : k = 4 := by
    norm_num [Nat.ModEq] at hcong
    omega
  exact ⟨T, hT, hCT, hk4⟩

private theorem exists_index_of_irreducible
    (b : PrimeCongruenceBlockData 5 G) {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacter χ) :
    ∃ i : b.I, ∀ g : G, b.chi i (ConjClasses.mk g) = χ g := by
  obtain ⟨n, ρ, hρ, rfl⟩ := hχ
  obtain ⟨i, hi⟩ := b.complete.2.1 (characterClassFunction ρ)
    ⟨⟨n, ρ, rfl⟩, (irreducible_iff_character_norm_one ρ).mp hρ⟩
  exact ⟨i, fun g => by rw [hi]; rfl⟩

variable [IsSimpleGroup G] {S : Sylow 2 G} {P : ABG.Wreathed.Presentation S 2}
  {d : PrincipalCongruenceBlockData G}

/-- The packet's four degrees, retaining the possible exchange of the two
negative constituents. -/
theorem four_degrees (c : Characters S P d) (i : Fin 4) :
    c.rational.four i 1 = 1 ∨ c.rational.four i 1 = 27 ∨
      c.rational.four i 1 = 21 ∨ c.rational.four i 1 = 7 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl c.degree_twenty_seven)
  · change _ ∨ _ ∨ c.rational.χ₃ 1 = 21 ∨ c.rational.χ₃ 1 = 7
    rw [c.rational.row₃_values.1]
    rcases c.conditions.classification.2 with ⟨h, _⟩ | ⟨_, h⟩ <;>
      simp [h]
  · change _ ∨ _ ∨ c.rational.χ₄ 1 = 21 ∨ c.rational.χ₄ 1 = 7
    rw [c.rational.row₄_values.1]
    rcases c.conditions.classification.2 with ⟨_, h⟩ | ⟨h, _⟩ <;>
      simp [h]

/-- All four actual rational irreducibles embed in the principal five-block;
neither their membership nor their distinctness is assumed. -/
theorem exists_four_five_block_rows (c : Characters S P d)
    (b : PrimeCongruenceBlockData 5 G) (T : Sylow 5 G) (hT : Nat.card T = 5)
    (hC : Subgroup.centralizer (T : Set G) = (T : Subgroup G)) :
    ∃ f : Fin 4 ↪ b.I, (∀ i, f i ∈ b.block) ∧
      (∀ i g, b.chi (f i) (ConjClasses.mk g) = c.rational.four i g) ∧
      (∀ i g, ∃ q : ℚ, b.chi (f i) (ConjClasses.mk g) = (q : ℂ)) := by
  classical
  choose f hf using fun i => exists_index_of_irreducible b (c.rational.four_irreducible i)
  have hinj : Function.Injective f := by
    intro i j hij
    apply c.rational.four_injective
    ext g
    rw [← hf i g, ← hf j g, hij]
  refine ⟨⟨f, hinj⟩, ?_, hf, ?_⟩
  · intro i
    rcases four_degrees c i with h | h | h | h
    · exact mem_block_of_prime_to_five_degree T hT hC b (f i) 1
        (by simpa using (hf i 1).trans h) (by decide)
    · exact mem_block_of_prime_to_five_degree T hT hC b (f i) 27
        ((hf i 1).trans h) (by decide)
    · exact mem_block_of_prime_to_five_degree T hT hC b (f i) 21
        ((hf i 1).trans h) (by decide)
    · exact mem_block_of_prime_to_five_degree T hT hC b (f i) 7
        ((hf i 1).trans h) (by decide)
  · intro i g
    obtain ⟨z, hz⟩ := c.rational.four_integer i g
    exact ⟨(z : ℚ), by simpa using (hf i g).trans hz⟩

/-- Final block contradiction once the full-automizer row construction is
supplied. The owning task must discharge this construction premise. -/
theorem five_centralizer_card_ne_five_of_rows (c : Characters S P d)
    (b : PrimeCongruenceBlockData 5 G)
    (hrows : ∀ T : Sylow 5 G, Nat.card T = 5 →
      Subgroup.centralizer (T : Set G) = (T : Subgroup G) →
      (Subgroup.centralizer (T : Set G)).relIndex
        (Subgroup.normalizer (T : Set G)) = 4 →
      Nonempty (CyclicFive.FullAutomizerRows b T))
    (hG : Nat.card G = 90720) {s : G} (hs : orderOf s = 5) :
    Nat.card (Subgroup.centralizer ({s} : Set G)) ≠ 5 := by
  intro hC
  obtain ⟨T, hT, hCT, hindex⟩ := exists_five_sylow_full_automizer hG hs hC
  obtain ⟨r⟩ := hrows T hT hCT hindex
  obtain ⟨f, hm, hf, _⟩ := exists_four_five_block_rows c b T hT hCT
  have hd : b.chi (f 1) (ConjClasses.mk 1) = (27 : ℤ) := by
    simpa [FongRationalConstituents.four] using (hf 1 1).trans c.degree_twenty_seven
  exact r.degree_not_two_mod_five hT (f 1) (hm 1) 27 hd (by decide)

/-- Fong's principal five-block obstruction, with the five-block datum and
full-automizer rows constructed from the given principal-block family.

The prime-five datum retains the ordinary irreducible family from `d` and
chooses a maximal ideal above five. Thus the block argument uses the actual
four rational constituents supplied by `c`, rather than assuming a separate
character family or row enumeration. -/
theorem five_centralizer_card_ne_five (c : Characters S P d)
    (hG : Nat.card G = 90720) {s : G} (hs : orderOf s = 5) :
    Nat.card (Subgroup.centralizer ({s} : Set G)) ≠ 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let b : PrimeCongruenceBlockData 5 G := {
    I := d.I
    fintypeI := d.fintypeI
    decidableEqI := d.decidableEqI
    chi := d.chi
    complete := d.complete
    eta := d.eta
    eta_spec := d.eta_spec
    primeIdeal := (exists_maximalIdeal_above_prime d.eta_spec 5).choose
    primeIdeal_maximal := (exists_maximalIdeal_above_prime d.eta_spec 5).choose_spec.1
    primeIdeal_liesOver := (exists_maximalIdeal_above_prime d.eta_spec 5).choose_spec.2
    principal := d.principal
    principal_eq := d.principal_eq }
  apply five_centralizer_card_ne_five_of_rows c b (fun T hT hCT hindex => ?_) hG hs
  exact CyclicFive.nonempty_fullAutomizerRows b T hT hCT hindex

end Stellmacher.Recognition.FongWreathed
