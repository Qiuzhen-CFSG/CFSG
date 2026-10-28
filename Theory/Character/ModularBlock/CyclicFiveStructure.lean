module

public import Theory.Character.ModularBlock.CyclicFiveRows
public import Theory.Character.CyclicFiveColumnArithmetic
public import Theory.Character.ConstantRestrictionIntegral
public import Theory.GroupTheory.PrimeOrderFullAutomizer

/-!
# The actual cyclic five-block with full automizer

The full automizer fuses the four nonidentity Sylow elements. Each ordinary
irreducible character is therefore constant there, and subgroup averaging
makes that constant rational. Character integrality makes it an integer.
Ordinary column orthogonality gives squared norm five and a vanishing
degree-weighted sum. These equations force exactly five nonzero entries,
all signs, with the principal character placed first.

Nonzero entries have degree prime to five by defect-zero vanishing and
belong to the principal block by self-centralization. Conversely a
principal-block member cannot vanish on the punctured Sylow subgroup.
Thus the enumeration is an equivalence onto the actual principal block.

Source: Fong (1967), printed p.75, citing Brauer (1942).
The ordinary column equations are adapted from `CyclicSevenColumnEquations`.
-/

public section
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace ModularBlock.CyclicFive
open PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]
variable {d : PrimeCongruenceBlockData 5 G} {P : Sylow 5 G}

private theorem centralizer_card (hP : Nat.card P = 5)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G)) (u : P) (hu : u ≠ 1) :
    Nat.card {x : G // x * (u : G) = (u : G) * x} = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hpow := pow_card_eq_one' (x := u)
  change u ^ Nat.card (P : Subgroup G) = 1 at hpow
  rw [hP] at hpow
  have huorder : orderOf (u : G) = 5 := by
    exact (Subgroup.orderOf_coe u).trans (orderOf_eq_prime
      hpow hu)
  have hz : Subgroup.zpowers (u : G) = (P : Subgroup G) := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr u.property)
    rw [Nat.card_zpowers, huorder]
    exact hP.le
  have hc : Subgroup.centralizer ({(u : G)} : Set G) = (P : Subgroup G) := by
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, hz]
    exact hC
  calc
    _ = Nat.card (Subgroup.centralizer ({(u : G)} : Set G)) :=
      Nat.card_congr (Equiv.subtypeEquivRight
        (fun _ => Subgroup.mem_centralizer_singleton_iff.symm))
    _ = 5 := by rw [hc]; exact hP

private theorem column_norm (hP : Nat.card P = 5)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G)) (u : P) (hu : u ≠ 1) :
    ∑ i, Complex.normSq (d.chi i (ConjClasses.mk (u : G))) = 5 := by
  classical
  obtain ⟨b, hb⟩ := completeFamily_form_basis d.complete
  have hc := centralizer_card hP hC u hu
  have hh := class_card_mul_centralizer_card (u : G)
  rw [hc] at hh
  have hpos : 0 < Nat.card (ConjClasses.mk (u : G)).carrier := by
    let : Nonempty (ConjClasses.mk (u : G)).carrier := ⟨⟨u, ConjClasses.mem_carrier_mk⟩⟩
    exact Nat.card_pos
  have he : (∑ i, d.chi i (ConjClasses.mk (u : G)) *
      star (d.chi i (ConjClasses.mk (u : G)))) = (5 : ℂ) := by
    rw [basis_sum_character_projection d.complete b hb, classProjection_apply_eq]
    apply (div_eq_iff (by exact_mod_cast hpos.ne')).mpr
    have hh' : (Nat.card (ConjClasses.mk (u : G)).carrier : ℂ) * 5 = (Nat.card G : ℂ) := by
      exact_mod_cast hh
    linear_combination -hh'
  have hr := congrArg Complex.re he
  simpa [Complex.re_sum, Complex.star_def, Complex.mul_conj] using hr

private theorem degree_column (u : P) (hu : u ≠ 1) :
    ∑ i, d.chi i (ConjClasses.mk (u : G)) * star (d.chi i (ConjClasses.mk 1)) = 0 := by
  classical
  obtain ⟨b, hb⟩ := completeFamily_form_basis d.complete
  rw [basis_sum_character_projection d.complete b hb]
  apply classProjection_apply_ne
  intro he
  apply hu
  apply Subtype.ext
  exact isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp he)

private theorem exists_integral_values (d : PrimeCongruenceBlockData 5 G)
    (P : Sylow 5 G) (hP : Nat.card P = 5)
    (hindex : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 4) (u : P) (hu : u ≠ 1) :
    ∃ b : d.I → ℤ, ∀ i (v : P), v ≠ 1 →
      d.chi i (ConjClasses.mk (v : G)) = (b i : ℂ) := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hv (i : d.I) (v : P) (hv : v ≠ 1) :
      d.chi i (ConjClasses.mk (v : G)) = d.chi i (ConjClasses.mk (u : G)) := by
    apply congrArg
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr
      ((P : Subgroup G).isConj_of_prime_card_full_automizer hP hindex v u hv hu)
  have hi (i : d.I) : ∃ z : ℤ, d.chi i (ConjClasses.mk (u : G)) = (z : ℂ) := by
    obtain ⟨n, ρ, hρ⟩ := (d.complete.1 i).1
    apply Representation.exists_int_of_character_constant (ρ.comp (P : Subgroup G).subtype)
      (by omega)
    intro v hv'
    have hh := hv i v hv'
    rw [hρ] at hh ⊢
    exact hh
  choose b hb using hi
  exact ⟨b, fun i v hv' => (hv i v hv').trans (hb i)⟩

/-- The actual principal five-block has five signed constant rows, with the
principal character first, when its order-five Sylow subgroup is
self-centralizing and has full automizer. -/
theorem nonempty_fullAutomizerRows (d : PrimeCongruenceBlockData 5 G)
    (P : Sylow 5 G) (hP : Nat.card P = 5)
    (hC : Subgroup.centralizer (P : Set G) = (P : Subgroup G))
    (hindex : (Subgroup.centralizer (P : Set G)).relIndex
      (Subgroup.normalizer (P : Set G)) = 4) :
    Nonempty (FullAutomizerRows d P) := by
  classical
  let : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : P)
  obtain ⟨b, hb⟩ := exists_integral_values d P hP hindex u hu
  have hdegree (i : d.I) : ∃ n : ℕ, d.chi i (ConjClasses.mk 1) = (n : ℂ) := by
    obtain ⟨n, ρ, hρ⟩ := (d.complete.1 i).1
    refine ⟨n, ?_⟩
    rw [hρ]
    change ρ.character 1 = (n : ℂ)
    simp
  choose n hn using hdegree
  have hp : b d.principal = 1 := by
    have hh := hb d.principal u hu
    simp [d.principal_eq, PrincipalBlockConstruction.ordinaryPrincipalCharacter] at hh
    exact_mod_cast hh.symm
  have hnp : (n d.principal : ℤ) = 1 := by
    have hh := hn d.principal
    simp [d.principal_eq, PrincipalBlockConstruction.ordinaryPrincipalCharacter] at hh
    exact_mod_cast hh.symm
  have hnorm : ∑ i, b i ^ 2 = 5 := by
    have hh := column_norm (d := d) hP hC u hu
    simp_rw [hb _ u hu, Complex.normSq_intCast] at hh
    have hh' : (∑ i, (b i : ℝ) ^ 2) = 5 := by simpa [pow_two] using hh
    exact_mod_cast hh'
  have horth : ∑ i, (n i : ℤ) * b i = 0 := by
    have hh := degree_column (d := d) u hu
    simp_rw [hb _ u hu, hn, star_natCast] at hh
    have hh' : (∑ i, (n i : ℂ) * (b i : ℂ)) = 0 := by
      simpa only [mul_comm] using hh
    exact_mod_cast hh'
  obtain ⟨e, he, hs, hz⟩ := CyclicFiveColumnArithmetic.exists_five_sign_rows
    b (fun i => (n i : ℤ)) d.principal hp hnp hnorm horth
  have hrow (j : Fin 5) : e j ∈ d.block := by
    apply mem_block_of_prime_to_five_degree P hP hC d _ (n (e j)) (hn (e j))
    apply degree_prime_to_five_of_value_ne_zero d P hP _ (n (e j)) (hn (e j)) u hu
    rw [hb _ u hu]
    rcases hs j with hh | hh <;> simp [hh]
  let f : Fin 5 → {i : d.I // i ∈ d.block} := fun j => ⟨e j, hrow j⟩
  have hf : Function.Bijective f := by
    refine ⟨fun j k h => e.injective (congrArg Subtype.val h), ?_⟩
    intro i
    have hirange : i.val ∈ Set.range e := by
      by_contra h
      obtain ⟨v, hv, hnv⟩ := exists_value_ne_zero_of_mem_block d P hP i.val i.property
      apply hnv
      rw [hb _ v hv, hz i.val h, Int.cast_zero]
    obtain ⟨j, hj⟩ := hirange
    exact ⟨j, Subtype.ext hj⟩
  exact ⟨{
    rows := Equiv.ofBijective f hf
    principal_row := he
    sign := fun j => b (e j)
    sign_unit := hs
    value := fun j v hv => hb (e j) v hv }⟩
end ModularBlock.CyclicFive
