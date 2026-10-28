module
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.PGroup
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The normalizer of a four-group fixing a pair in A₇

An elementary four-group fixing two letters fixes exactly three: a nonidentity
involution moves four letters, and the fixed-point congruence gives odd parity.
It is the Klein four-group on the remaining four letters, so its normalizer
is precisely the setwise stabilizer of the same triple, of order 72.

Source application: Aschbacher–Smith 5.2.11(2), printed pp.653–654
(`refs/quasithin.pdf`). The source consumer retains the quotient map and both
original pair subgroups while pulling back this triple stabilizer.
-/

public noncomputable section
open Subgroup MulAction
open scoped Pointwise
namespace Theory.GroupTheory.QuasithinM23
local notation "A7" => alternatingGroup (Fin 7)

private theorem involution_cycleType (x : A7) (hx : orderOf x = 2) :
    x.val.cycleType = {2,2} := by
  have ho : orderOf x.val = 2 := (Subgroup.orderOf_coe x).trans hx
  obtain ⟨k,hk⟩ := Equiv.Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hb := x.val.sum_cycleType_le
  rw [hk] at hb
  simp only [Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,Fintype.card_fin] at hb
  have hs := Equiv.Perm.mem_alternatingGroup.mp x.property
  rw [Equiv.Perm.sign_of_cycleType',hk] at hs
  have hk2 : k ≤ 2 := by omega
  have hk1 : k = 1 := by
    interval_cases k
    · norm_num at hs
    · rfl
    · norm_num at hs
  simpa [hk1] using hk

/-- A four-group fixing a pair in the seven-point action fixes exactly a
triple, and its normalizer is the setwise stabilizer of that same triple. -/
theorem four_fixing_pair_normalizer
    (Q : Subgroup A7) [IsElementaryAbelian 2 Q] (hQ : Nat.card Q = 4)
    (i j : Fin 7) (hij : i ≠ j)
    (hi : ∀ q : Q, q.val.val i = i) (hj : ∀ q : Q, q.val.val j = j) :
    ∃ s : Finset (Fin 7), s.card = 3 ∧ i ∈ s ∧ j ∈ s ∧
      (∀ k : Fin 7, k ∈ s ↔ ∀ q : Q, q.val.val k = k) ∧
      normalizer (Q : Set A7) = stabilizer A7 (s : Set (Fin 7)) := by
  classical
  let s := (fixedPoints Q (Fin 7)).toFinset
  have hs_mem (k : Fin 7) : k ∈ s ↔ ∀ q : Q, q.val.val k = k := by
    simp only [s,Set.mem_toFinset]
    rfl
  have hi' : i ∈ s := (hs_mem i).mpr hi
  have hj' : j ∈ s := (hs_mem j).mpr hj
  have hlow : 2 ≤ s.card := by
    have hh := Finset.card_le_card (show ({i,j} : Finset (Fin 7)) ⊆ s by
      intro k hk; rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hk : k=i ∨ k=j) with rfl | rfl <;> assumption)
    simpa only [Finset.card_pair hij] using hh
  have : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,hx⟩ := exists_ne (1 : Q)
  have hx1 : x.val ≠ 1 := fun he => hx (Subtype.ext he)
  have hx2 : orderOf x.val = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian x.val x.property) hx1
  have hxct := involution_cycleType x.val hx2
  have hupp : s.card ≤ 3 := by
    have hle : s ⊆ x.val.val.supportᶜ := by
      intro k hk
      rw [Finset.mem_compl,Equiv.Perm.notMem_support]
      exact (hs_mem k).mp hk x
    have hh := Finset.card_le_card hle
    rw [Finset.card_compl,←Equiv.Perm.sum_cycleType,hxct] at hh
    norm_num at hh ⊢
    exact hh
  have hp := (IsPGroup.of_card (p := 2) (n := 2) hQ).card_modEq_card_fixedPoints (Fin 7)
  have hcfix : Nat.card (fixedPoints Q (Fin 7)) = s.card := by
    simp [s,Nat.card_eq_fintype_card]
  rw [Nat.card_fin,hcfix] at hp
  have hs : s.card = 3 := by
    change 7 % 2 = s.card % 2 at hp
    omega
  have hs4 : sᶜ.card = 4 := by rw [Finset.card_compl,hs]; rfl
  let K := (alternatingGroup.kleinFour ↥(sᶜ)).map (alternatingGroup.ofSubtype sᶜ)
  have hQK : Q ≤ K := by
    intro q hq
    apply (alternatingGroup.mem_map_kleinFour_ofSubtype hs4 q).mpr
    constructor
    · intro k hk
      rw [Finset.mem_compl]
      intro hks
      exact (Equiv.Perm.mem_support.mp hk) ((hs_mem k).mp hks ⟨q,hq⟩)
    · by_cases hq1 : q = 1
      · left; exact congrArg Subtype.val hq1
      · right
        exact involution_cycleType q (orderOf_eq_prime
          (elemPow_eq_one_of_isElementaryAbelian q hq) hq1)
  have hKcard : Nat.card K = 4 := by
    rw [card_map_of_injective alternatingGroup.ofSubtype_injective,
      alternatingGroup.kleinFour_card_of_card_eq_four (by simp [hs])]
  have hQK : Q = K := eq_of_le_of_card_ge hQK (by rw [hKcard,hQ])
  have hmem (q : A7) : q ∈ Q ↔ (∀ k ∈ s, q.val k = k) ∧ q^2=1 := by
    constructor
    · intro hq
      exact ⟨fun k hk => (hs_mem k).mp hk ⟨q,hq⟩,
        elemPow_eq_one_of_isElementaryAbelian q hq⟩
    · rintro ⟨hqfix,hq2⟩
      rw [hQK]
      apply (alternatingGroup.mem_map_kleinFour_ofSubtype hs4 q).mpr
      refine ⟨?_,?_⟩
      · intro k hk
        rw [Finset.mem_compl]
        exact fun hks => (Equiv.Perm.mem_support.mp hk) (hqfix k hks)
      · by_cases hq1 : q = 1
        · exact Or.inl (congrArg Subtype.val hq1)
        · exact Or.inr (involution_cycleType q (orderOf_eq_prime hq2 hq1))
  refine ⟨s,hs,hi',hj',hs_mem,le_antisymm ?_ ?_⟩
  · intro g hg
    apply (mem_stabilizer_set' (Set.toFinite _)).mpr
    intro k hk
    apply (hs_mem _).mpr
    intro q
    have hq := (mem_normalizer_iff''.mp hg q.val).mp q.property
    have hh := (hs_mem k).mp hk ⟨g⁻¹*q.val*g,hq⟩
    have he := congrArg (fun a : Fin 7 => g.val a) hh
    change q.val.val (g.val k) = g.val k
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,Equiv.Perm.coe_mul,
      Function.comp_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using he
  · intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨q,hq,rfl⟩
      apply (hmem _).mpr
      constructor
      · intro k hk
        have hg' := (stabilizer A7 (s : Set (Fin 7))).inv_mem hg
        have hk' := (mem_stabilizer_set' (Set.toFinite _)).mp hg' hk
        have hh := (hmem q).mp hq
        change g.val.symm k ∈ s at hk'
        change g.val (q.val (g.val.symm k)) = k
        rw [hh.1 _ hk',Equiv.apply_symm_apply]
      · change ((MulAut.conj g) q)^2=1
        rw [←map_pow,(hmem q).mp hq |>.2,map_one]
    · rw [card_map_of_injective (MulAut.conj g).injective]

/-- The actual alternating seven-point triple stabilizer has order 72. -/
theorem seven_triple_stabilizer_card (s : Finset (Fin 7)) (hs : s.card = 3) :
    Nat.card (stabilizer A7 (s : Set (Fin 7))) = 72 := by
  let t : Set.powersetCard (Fin 7) 3 := ⟨s,hs⟩
  have htrans : IsMultiplyPretransitive A7 (Fin 7) 3 := by
    let : IsMultiplyPretransitive A7 (Fin 7) 5 := by
      simpa only [Nat.card_fin] using alternatingGroup.isMultiplyPretransitive (Fin 7)
    exact isMultiplyPretransitive_of_le (G := A7) (α := Fin 7) (n := 5) (by decide) (by simp)
  let : IsMultiplyPretransitive A7 (Fin 7) 3 := htrans
  let : IsPretransitive A7 (Set.powersetCard (Fin 7) 3) :=
    Set.powersetCard.isPretransitive_of_isMultiplyPretransitive A7 htrans
  have hi : (stabilizer A7 (s : Set (Fin 7))).index = 35 := by
    change (stabilizer A7 (t : Set (Fin 7))).index = 35
    rw [←Set.powersetCard.stabilizer_coe t]
    have hh := index_stabilizer_of_transitive (G := A7) t
    rw [Set.powersetCard.card, Nat.card_fin] at hh
    exact hh
  have hc := (stabilizer A7 (s : Set (Fin 7))).card_mul_index
  rw [hi,nat_card_alternatingGroup] at hc
  have ha : Nat.card A7 = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [←nat_card_alternatingGroup, ha] at hc
  omega

end Theory.GroupTheory.QuasithinM23
