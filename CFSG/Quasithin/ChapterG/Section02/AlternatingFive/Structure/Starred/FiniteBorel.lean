module

public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Theory.GroupTheory.PCoreImage

/-!
# The finite Borel calculations used by G.2.4

The four double transpositions fixing a specified letter form the actual
Sylow four-group of A₅ and the two-core of the embedded A₄ stabilizer.
An odd element of S₄ has a nontrivial cubic commutator with A₄, so a
two-subgroup normalized by A₄ is even. The cubic conjugation orbit on the
three involutions then makes every such nontrivial subgroup the full four-group.
The same cubic gives the full commutator identity. Two different four-groups
supply an element of order five; divisibility and the faithful coset action
of the simple A₅ force their join to be all of A₅.

Only small permutation identities are checked by kernel reduction. The
subgroup and generation arguments are structural, and retain the specified
coordinate and conjugation convention.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(1–2), printed p.334, referring to G.2.3, pp.333–334.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Starred.FiniteBorel
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

private def base : Fin 4 → S5 :=
  ![1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]
private def word (i : Fin 5) (k : Fin 4) : S5 :=
  MulAut.conj (Equiv.swap 4 i) (base k)
private theorem word_zero (i : Fin 5) : word i 0 = 1 := map_one _
private theorem word_injective (i : Fin 5) : Function.Injective (word i) :=
  (MulAut.conj (Equiv.swap 4 i)).injective.comp (by decide +kernel)

def four (i : Fin 5) : Subgroup S5 where
  carrier := Set.range (word i)
  one_mem' := ⟨0, word_zero i⟩
  mul_mem' := by
    have hc : ∀ k l, ∃ m, base k * base l = base m := by decide +kernel
    rintro x y ⟨k, rfl⟩ ⟨l, rfl⟩
    obtain ⟨m, hm⟩ := hc k l
    exact ⟨m, by rw [word, ← hm, map_mul]; rfl⟩
  inv_mem' := by
    have hc : ∀ k, (base k)⁻¹ = base k := by decide +kernel
    rintro x ⟨k, rfl⟩
    exact ⟨k, by rw [word, ← map_inv, hc]⟩

private theorem mem_four (i : Fin 5) (s : S5) : s ∈ four i ↔ ∃ k, word i k = s := Iff.rfl

private theorem four_criterion (i : Fin 5) (s : S5) :
    s ∈ four i ↔ s i = i ∧ s.sign = 1 ∧ s ^ 2 = 1 := by
  have h : ∀ i : Fin 5, ∀ s : S5,
      (∃ k, word i k = s) ↔ s i = i ∧ s.sign = 1 ∧ s ^ 2 = 1 := by decide +kernel
  exact h i s

@[expose] def borel (i : Fin 5) : Subgroup S5 := A5 ⊓ MulAction.stabilizer S5 i

theorem four_le_borel (i : Fin 5) : four i ≤ borel i := by
  intro x hx
  have h := (four_criterion i x).mp hx
  exact ⟨Equiv.Perm.mem_alternatingGroup.mpr h.2.1, h.1⟩

theorem four_card (i : Fin 5) : Nat.card (four i) = 4 := by
  change Nat.card (Set.range (word i)) = 4
  rw [← Nat.card_congr (Equiv.ofInjective _ (word_injective i))]
  simp

theorem four_isPGroup (i : Fin 5) : IsPGroup 2 (four i) :=
  IsPGroup.of_card (n := 2) (four_card i)

theorem borel_normalizes_four (i : Fin 5) : borel i ≤ normalizer (four i : Set S5) := by
  apply le_normalizer_iff.mpr
  intro b hb x hx
  have hx := (four_criterion i x).mp hx
  apply (four_criterion i _).mpr
  have hbi : b i = i := hb.2
  have hbinv : b⁻¹ i = i := b.injective (by simpa using hbi.symm)
  refine ⟨?_, ?_, ?_⟩
  · change b (x (b⁻¹ i)) = i
    rw [hbinv, hx.1, hbi]
  · rw [map_mul, map_mul, map_inv, hx.2.1, mul_one, mul_inv_cancel]
  · change (MulAut.conj b x) ^ 2 = 1
    rw [← map_pow, hx.2.2, map_one]

/-- The literal four-group, viewed inside A₅, is Sylow. -/
noncomputable def fourSylow (i : Fin 5) : Sylow 2 A5 :=
  Sylow.ofCard ((four i).subgroupOf A5) (by
    rw [Nat.card_congr (subgroupOfEquivOfLe ((four_le_borel i).trans inf_le_left)).toEquiv,
      four_card, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    rw [show 60 = 2 ^ 2 * 15 by decide, Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply, Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)]
    rfl)

theorem fourSylow_map (i : Fin 5) :
    ((fourSylow i : Sylow 2 A5) : Subgroup A5).map (A5).subtype = four i :=
  map_subgroupOf_eq_of_le ((four_le_borel i).trans inf_le_left)

theorem four_eq_core (i : Fin 5) : four i = (borel i).pCoreIn 2 := by
  have hle := le_pCoreIn_of_normalizes (four_isPGroup i) (four_le_borel i)
    (borel_normalizes_four i)
  have hc : (borel i).pCoreIn 2 ≤ A5 := (pCoreIn_le 2 _).trans inf_le_left
  have he := (fourSylow i).is_maximal'
    ((isPGroup_pCoreIn 2 (borel i)).comap_subtype)
    (comap_mono hle : (four i).subgroupOf A5 ≤ ((borel i).pCoreIn 2).subgroupOf A5)
  have hm := congrArg (Subgroup.map (A5).subtype) he
  change (((borel i).pCoreIn 2).subgroupOf A5).map (A5).subtype =
    ((fourSylow i : Sylow 2 A5) : Subgroup A5).map (A5).subtype at hm
  rw [map_subgroupOf_eq_of_le hc, fourSylow_map] at hm
  exact hm.symm

private def cubic (i : Fin 5) : S5 :=
  MulAut.conj (Equiv.swap 4 i) (Equiv.swap 0 1 * Equiv.swap 1 2)
private theorem cubic_mem (i : Fin 5) : cubic i ∈ borel i := by
  have h : ∀ i : Fin 5, (cubic i).sign = 1 ∧ cubic i i = i := by decide +kernel
  exact ⟨Equiv.Perm.mem_alternatingGroup.mpr (h i).1, (h i).2⟩

private theorem cubic_transitive (i : Fin 5) (k l : Fin 4) (hk : k ≠ 0) :
    l = 0 ∨ ∃ n : Fin 3, cubic i ^ n.val * word i k * (cubic i ^ n.val)⁻¹ = word i l := by
  have h : ∀ (i : Fin 5) (k l : Fin 4), k ≠ 0 →
      l = 0 ∨ ∃ n : Fin 3, cubic i ^ n.val * word i k * (cubic i ^ n.val)⁻¹ = word i l := by
    decide +kernel
  exact h i k l hk

private theorem no_cubic (U : Subgroup S5) (hU : IsPGroup 2 U)
    (x : S5) (hx : x ∈ U) (hp : x ^ 3 = 1) : x = 1 := by
  have he : (⟨x, hx⟩ : U) ^ 3 = 1 := Subtype.ext hp
  have hc := (hU.powEquiv (by decide : Nat.Coprime 2 3)).injective
    (he.trans (one_pow 3).symm)
  exact congrArg Subtype.val hc

/-- A nontrivial two-subgroup of S₄ normalized by its A₄ is its four-group. -/
theorem normalized_two_eq_four (i : Fin 5) (U : Subgroup S5)
    (hU : IsPGroup 2 U) (hne : U ≠ ⊥)
    (hfix : U ≤ MulAction.stabilizer S5 i) (hn : borel i ≤ normalizer (U : Set S5)) :
    U = four i := by
  have heven : U ≤ A5 := by
    intro x hx
    apply Equiv.Perm.mem_alternatingGroup.mpr
    by_contra ho
    obtain ⟨b, hb, hp, hne⟩ :=
      Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.odd_actor_cubic_witness i x (hfix hx) ho
    have hcomm : ⁅b, x⁆ ∈ U := by
      exact U.mul_mem ((mem_normalizer_iff.mp (hn hb) x).mp hx) (U.inv_mem hx)
    exact hne (no_cubic U hU _ hcomm hp)
  have hle : U ≤ four i := by
    intro x hx
    apply (four_criterion i x).mpr
    have he : x.sign = 1 := Equiv.Perm.mem_alternatingGroup.mp (heven hx)
    refine ⟨hfix hx, he, ?_⟩
    have ht : ∀ (i : Fin 5) (x : S5), x i = i → x.sign = 1 → x ^ 2 = 1 ∨ x ^ 3 = 1 := by
      decide +kernel
    rcases ht i x (hfix hx) he with h | h
    · exact h
    · rw [no_cubic U hU _ hx h, one_pow]
  apply le_antisymm hle
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨k, hk⟩ := (mem_four i x).mp (hle x.property)
  have hk0 : k ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    exact hk.symm.trans (h ▸ word_zero i)
  rintro y ⟨l, rfl⟩
  rcases cubic_transitive i k l hk0 with rfl | ⟨n, hn'⟩
  · rw [word_zero]
    exact U.one_mem
  · rw [← hn']
    exact (mem_normalizer_iff.mp (hn ((borel i).pow_mem (cubic_mem i) n.val)) _).mp
      (hk ▸ x.property)

theorem four_commutator (i : Fin 5) : ⁅four i, borel i⁆ = four i := by
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp (borel_normalizes_four i))
  have hc : ∀ (i : Fin 5) (k : Fin 4), ∃ l : Fin 4,
      ⁅word i l, cubic i⁆ = word i k := by decide +kernel
  rintro x ⟨k, rfl⟩
  obtain ⟨l, hl⟩ := hc i k
  rw [← hl]
  exact commutator_mem_commutator ⟨l, rfl⟩ (cubic_mem i)

/-- Distinct marked four-groups generate A₅. -/
theorem distinct_four_generate (i j : Fin 5) (hij : i ≠ j) : four i ⊔ four j = A5 := by
  let J := four i ⊔ four j
  have hJA : J ≤ A5 := sup_le ((four_le_borel i).trans inf_le_left)
    ((four_le_borel j).trans inf_le_left)
  let M := J.subgroupOf A5
  let : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  have hfour : 4 ∣ Nat.card J := by
    rw [← four_card i]
    exact card_dvd_of_le (show four i ≤ J from le_sup_left)
  have hfive : 5 ∣ Nat.card J := by
    have hc : ∀ (i j : Fin 5), i ≠ j → ∃ k l : Fin 4,
        (word i k * word j l) ^ 5 = 1 ∧ word i k * word j l ≠ 1 := by decide +kernel
    obtain ⟨k, l, hp, hn⟩ := hc i j hij
    let x : J := ⟨word i k * word j l, J.mul_mem (mem_sup_left ⟨k, rfl⟩) (mem_sup_right ⟨l, rfl⟩)⟩
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have ho : orderOf x = 5 :=
      (orderOf_eq_prime_iff).mpr
        ⟨Subtype.ext hp, fun h => hn (congrArg Subtype.val h)⟩
    have hd := _root_.orderOf_dvd_natCard x
    rw [ho] at hd
    exact hd
  have htwenty : 20 ∣ Nat.card J :=
    (show Nat.Coprime 4 5 by decide).mul_dvd_of_dvd_of_dvd hfour hfive
  have hcard : Nat.card A5 = 60 := by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  have hM : Nat.card M = Nat.card J := Nat.card_congr (subgroupOfEquivOfLe hJA).toEquiv
  have hpos := Nat.card_pos (α := J)
  have hi := M.card_mul_index
  rw [hM, hcard] at hi
  have hlow : 20 ≤ Nat.card J := Nat.le_of_dvd hpos htwenty
  have hind : M.index ≤ 3 := by nlinarith
  have htop : M = ⊤ := by
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have h := Nat.factorial_le hind
    rw [hcard]
    norm_num [Nat.factorial] at h ⊢
    omega
  have he := congrArg (Subgroup.map (A5).subtype) htop
  rw [map_subgroupOf_eq_of_le hJA, ← MonoidHom.range_eq_map, range_subtype] at he
  exact he

/-- Conjugation changes precisely the derived fixed coordinate. -/
theorem four_conjugate (i : Fin 5) (s : S5) :
    (four i).map (MulAut.conj s).toMonoidHom = four (s i) := by
  ext x
  rw [mem_map_equiv]
  change s⁻¹ * x * s ∈ four i ↔ x ∈ four (s i)
  rw [four_criterion, four_criterion]
  have hsign : (s⁻¹ * x * s).sign = x.sign := by
    rw [map_mul, map_mul, map_inv, mul_comm (s.sign)⁻¹ (x.sign), mul_assoc,
      inv_mul_cancel, mul_one]
  have hsquare : (s⁻¹ * x * s) ^ 2 = 1 ↔ x ^ 2 = 1 := by
    change (MulAut.conj s⁻¹ x) ^ 2 = 1 ↔ _
    rw [← map_pow]
    exact (MulAut.conj s⁻¹).map_eq_one_iff
  rw [hsign, hsquare]
  apply and_congr_left
  intro _
  change s⁻¹ (x (s i)) = i ↔ x (s i) = s i
  exact s.symm_apply_eq

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Starred.FiniteBorel
