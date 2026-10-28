module

public import Theory.GroupAction.CoprimeNormalizerDecomposition
public import Theory.GroupAction.FiveSixteenCentralizer
public import Theory.GroupTheory.ElementaryEightSevenNormalizer
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.Fitting.Core
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Five- and seven-cores of automorphism groups on thirty-two elements

In GL(5,2), a five-subgroup has normalizer order dividing sixty, and a
seven-subgroup has normalizer order not divisible by four. Coprime
splitting gives fixed and moving factors of orders 2 and 16, or 4 and 8.
The existing sixteen-element centralizer bound and eight-element seven
normalizer bound control the action on the moving factor.

The five- and seven-parts of |GL(5,2)| are prime. Thus a nontrivial core
has prime order, and its normalizer contains the whole automorphism
subgroup. The normalizer bounds exclude those cores whenever respectively
eight or four divides the subgroup order. In particular both vanish for
subgroups of order 64*n, without any solvability or restrictions on n.

Source: Parrott, A Characterization of the Tits' Simple Group (1972),
printed p.673, properties (1), (5), (6), used on p.677 after Lemma 5.
-/

open scoped IsMulCommutative
open Subgroup

private instance elementary_subgroup
    {E : Type*} [Group E] [IsElementaryAbelian 2 E] (D : Subgroup E) :
    IsElementaryAbelian 2 D where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
    (IsElementaryAbelian.exponent_dvd_p 2 E)

private theorem fixed_card_five_or_seven
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 32)
    (p : ℕ) [Fact p.Prime] (hp : p = 5 ∨ p = 7)
    (A : Subgroup (MulAut E)) (hA : Nat.card A = p) :
    Nat.card (FixedPoints.subgroup A E) = 32 % p := by
  let F := FixedPoints.subgroup A E
  have hmod := (IsPGroup.of_card (p := p) (G := A) (n := 1)
    (by simpa using hA)).card_modEq_card_fixedPoints E
  change Nat.card E % p = Nat.card F % p at hmod
  rw [hE] at hmod
  have hdiv : Nat.card F ∣ 32 := hE ▸ F.card_subgroup_dvd_card
  have hproper : Nat.card F ≠ 32 := by
    intro hh
    have htop : F = ⊤ := F.eq_top_of_card_eq (hh.trans hE.symm)
    have hbot : A = ⊥ := by
      apply eq_bot_iff.mpr
      intro a ha
      apply mem_bot.mpr
      apply MulEquiv.ext
      intro x
      have hx : x ∈ F := htop ▸ mem_top x
      exact hx ⟨a, ha⟩
    rw [hbot, card_bot] at hA
    rcases hp with rfl | rfl <;> omega
  have hmem := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
  have hdivs : (32 : ℕ).divisors = {1, 2, 4, 8, 16, 32} := by decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  change Nat.card F = 32 % p
  rcases hp with rfl | rfl <;> omega

private theorem card_fixed_mul_moving
    {E : Type*} [Group E] [Finite E] [IsMulCommutative E]
    (A : Subgroup (MulAut E)) (hcop : Nat.Coprime (Nat.card A) (Nat.card E)) :
    Nat.card (FixedPoints.subgroup A E) * Nat.card (commutatorAction A E) =
      Nat.card E := by
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := E) (A := A) (Group.isSolvable_of_comm (fun a b : E => mul_comm a b))
      hcop inferInstance
  have hh := card_sup_eq_mul_of_normalizes_of_disjoint (FixedPoints.subgroup A E)
    (commutatorAction A E) (by rw [normalizer_eq_top]; exact le_top) hcompl.disjoint
  rw [hcompl.sup_eq_top, card_top] at hh
  exact hh.symm

private theorem card_normalizer_five_sixteen_dvd_sixty
    {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 16)
    (A : Subgroup (MulAut V)) (hA : Nat.card A = 5) :
    Nat.card (normalizer (A : Set (MulAut V))) ∣ 60 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic A := isCyclic_of_prime_card hA
  have hAut : Nat.card (MulAut A) = 4 := by
    rw [IsCyclic.card_mulAut, hA]
    decide
  let f := A.normalizerMonoidHom
  have hrange : Nat.card f.range ∣ 4 := hAut ▸ f.range.card_subgroup_dvd_card
  have hker : Nat.card f.ker ∣ 15 := by
    have hc := card_centralizer_five_dvd_fifteen (V := V) A hA hV
    have heq : Nat.card f.ker = Nat.card (centralizer (A : Set (MulAut V))) := by
      rw [normalizerMonoidHom_ker,
        Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set (MulAut V)))).toEquiv]
    rwa [heq]
  have hh := Nat.mul_dvd_mul hker hrange
  have hprod := f.ker.card_mul_index
  rw [index_ker] at hprod
  simpa only [hprod] using hh

/-- A five-subgroup on an elementary group of order thirty-two has normalizer
order dividing sixty. -/
public theorem card_normalizer_of_elementary_thirtytwo_five_dvd_sixty
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (A : Subgroup (MulAut E)) (hA : Nat.card A = 5) :
    Nat.card (normalizer (A : Set (MulAut E))) ∣ 60 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hcop : Nat.Coprime (Nat.card A) (Nat.card E) := by rw [hA, hE]; decide
  have hF : Nat.card (FixedPoints.subgroup A E) = 2 :=
    fixed_card_five_or_seven hE 5 (Or.inl rfl) A hA
  have hC : Nat.card (commutatorAction A E) = 16 := by
    have hh := card_fixed_mul_moving A hcop
    rw [hF, hE] at hh
    omega
  have hAut : Nat.card (MulAut (FixedPoints.subgroup A E)) = 1 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 1 (by simpa using hF)]
    decide
  obtain ⟨D, hD, hdiv⟩ := exists_restricted_coprime_normalizer A hcop
  rw [hAut, one_mul] at hdiv
  exact hdiv.trans (card_normalizer_five_sixteen_dvd_sixty hC D (hD.trans hA))

/-- A seven-subgroup on an elementary group of order thirty-two has normalizer
order not divisible by four. -/
public theorem not_four_dvd_card_normalizer_of_elementary_thirtytwo_seven
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (A : Subgroup (MulAut E)) (hA : Nat.card A = 7) :
    ¬ 4 ∣ Nat.card (normalizer (A : Set (MulAut E))) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hcop : Nat.Coprime (Nat.card A) (Nat.card E) := by rw [hA, hE]; decide
  have hF : Nat.card (FixedPoints.subgroup A E) = 4 :=
    fixed_card_five_or_seven hE 7 (Or.inr rfl) A hA
  have hC : Nat.card (commutatorAction A E) = 8 := by
    have hh := card_fixed_mul_moving A hcop
    rw [hF, hE] at hh
    omega
  have hAut : Nat.card (MulAut (FixedPoints.subgroup A E)) = 6 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 2 (by simpa using hF)]
    decide
  obtain ⟨D, hD, hdiv⟩ := exists_restricted_coprime_normalizer A hcop
  rw [hAut] at hdiv
  have hodd := odd_card_normalizer_of_elementary_eight_seven _ hC D (hD.trans hA)
  intro hfour
  have hh : 4 ∣ 6 :=
    (hodd.coprime_two_left.pow_left 2).dvd_of_dvd_mul_right (hfour.trans hdiv)
  norm_num at hh

private theorem core_eq_bot_of_normalizer_obstruction
    {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (d : ℕ) (hd : d ∣ Nat.card B)
    (p : ℕ) [Fact p.Prime] (hnot : ¬ p ^ 2 ∣ Nat.card G)
    (hnorm : ∀ A : Subgroup G, Nat.card A = p →
      ¬ d ∣ Nat.card (normalizer (A : Set G))) : pCore p B = ⊥ := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := B)).exists_card_eq
  have hdiv : p ^ n ∣ Nat.card G := by
    rw [← hn]
    exact dvd_trans (pCore p B).card_subgroup_dvd_card B.card_subgroup_dvd_card
  have hnle : n ≤ 1 := by
    by_contra! hh
    exact hnot (dvd_trans (pow_dvd_pow p hh) hdiv)
  by_cases hz : n = 0
  · apply Subgroup.card_eq_one.mp
    simpa only [hz, pow_zero] using hn
  have hn1 : n = 1 := by omega
  have hcard : Nat.card (pCore p B) = p := by simpa only [hn1, pow_one] using hn
  let A := (pCore p B).map B.subtype
  have hA : Nat.card A = p := by
    rw [card_map_of_injective B.subtype_injective]
    exact hcard
  have hle : B ≤ normalizer (A : Set G) := by
    have hh := (pCore p B).le_normalizer_map B.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, B.range_subtype] using hh
  exact (hnorm A hA (dvd_trans hd (card_dvd_of_le hle))).elim

private theorem card_aut_thirtytwo
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) : Nat.card (MulAut E) = 9999360 := by
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E 5 (by simpa using hE)]
  decide

/-- Eight-divisibility excludes the five-core of an automorphism subgroup on
an elementary group of order thirty-two. -/
public theorem pCore_five_eq_bot_of_elementary_thirtytwo
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (B : Subgroup (MulAut E)) (hB : 8 ∣ Nat.card B) :
    pCore 5 B = ⊥ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply core_eq_bot_of_normalizer_obstruction B 8 hB 5
  · rw [card_aut_thirtytwo E hE]
    decide
  · intro A hA hdiv
    have hh := hdiv.trans (card_normalizer_of_elementary_thirtytwo_five_dvd_sixty hE A hA)
    norm_num at hh

/-- Four-divisibility excludes the seven-core of an automorphism subgroup on
an elementary group of order thirty-two. -/
public theorem pCore_seven_eq_bot_of_elementary_thirtytwo
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (B : Subgroup (MulAut E)) (hB : 4 ∣ Nat.card B) :
    pCore 7 B = ⊥ := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply core_eq_bot_of_normalizer_obstruction B 4 hB 7
  · rw [card_aut_thirtytwo E hE]
    decide
  · exact fun A hA =>
      not_four_dvd_card_normalizer_of_elementary_thirtytwo_seven hE A hA

/-- Both odd prime cores vanish when the automorphism subgroup order is 64*n.
No solvability, parity, or upper bound on n is needed. -/
public theorem five_seven_cores_eq_bot_of_elementary_thirtytwo_card
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (B : Subgroup (MulAut E))
    (n : ℕ) (hB : Nat.card B = 64 * n) : pCore 5 B = ⊥ ∧ pCore 7 B = ⊥ := by
  constructor
  · apply pCore_five_eq_bot_of_elementary_thirtytwo hE B
    rw [hB]
    exact dvd_mul_of_dvd_left (by decide : 8 ∣ 64) n
  · apply pCore_seven_eq_bot_of_elementary_thirtytwo hE B
    rw [hB]
    exact dvd_mul_of_dvd_left (by decide : 4 ∣ 64) n
