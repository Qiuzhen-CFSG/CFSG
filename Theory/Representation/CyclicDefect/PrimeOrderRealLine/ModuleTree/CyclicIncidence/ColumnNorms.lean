module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.LocalInertia
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.ColumnNorms.RecognitionData
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.ColumnNorms.Restriction
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.Combinatorics

/-!
# The final restriction argument for cyclic decomposition columns

A local difference of characters gives a sign on each ordinary block row.
Thompson's bound applied to the positive and negative subcharacters permits
at most one constituent of each sign. Singular vanishing makes the signed
sum zero. A nonzero column therefore has squared norm two, and the finite
endpoint theorem gives its exact two zero-one entries.

This proves the terminal argument of Feit VII.5.6--7 and VII.2.15 (printed
pp.292,299), for the exact numbers in the supplied `Decomposition`. The
source obligations remain explicit: recognition as principal projectives,
singular vanishing, the local-character construction and unit row
restrictions from VII.2.11--14, and the Thompson bound VII.5.6. In particular
this module does not yet prove the column theorem from `PrimeOrderInput`
and `n = p - 1` alone.
-/

public section
noncomputable section
open scoped BigOperators Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.ColumnNorms
open ModularBlock.PrimeBlockConstruction

private theorem sum_sq_eq_two_of_signed_subsums {V : Type*} [Fintype V]
    (f : V → ℕ) (ε : V → ℤ) (hε : ∀ v, ε v = 1 ∨ ε v = -1)
    (hne : ∃ v, f v ≠ 0) (hzero : ∑ v, (f v : ℤ) * ε v = 0)
    (hbound : ∀ c : V → ℕ, (∀ v, c v ≤ f v) →
      -1 ≤ ∑ v, (c v : ℤ) * ε v ∧ ∑ v, (c v : ℤ) * ε v ≤ 1) :
    ∑ v, f v ^ 2 = 2 := by
  let pos (v : V) : ℕ := if ε v = 1 then f v else 0
  let neg (v : V) : ℕ := if ε v = -1 then f v else 0
  have hp (v : V) : pos v ≤ f v := by simp [pos]; split_ifs <;> omega
  have hn (v : V) : neg v ≤ f v := by simp [neg]; split_ifs <;> omega
  have hsplit (v : V) : f v = pos v + neg v := by
    rcases hε v with hv | hv <;> simp [pos, neg, hv]
  have hpos : (∑ v, (pos v : ℤ) * ε v) = ((∑ v, pos v : ℕ) : ℤ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : ε v = 1 <;> simp [pos, hv]
  have hneg : (∑ v, (neg v : ℤ) * ε v) = -((∑ v, neg v : ℕ) : ℤ) := by
    rw [Nat.cast_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : ε v = -1 <;> simp [neg, hv]
  have hbal : (∑ v, pos v) = ∑ v, neg v := by
    have hz : ((∑ v, pos v : ℕ) : ℤ) - ((∑ v, neg v : ℕ) : ℤ) = 0 := by
      rw [sub_eq_add_neg, ← hpos, ← hneg, ← Finset.sum_add_distrib]
      simp_rw [← add_mul, ← Nat.cast_add, ← hsplit]
      exact hzero
    exact_mod_cast sub_eq_zero.mp hz
  have hp1 : ∑ v, pos v ≤ 1 := by
    have hh := (hbound pos hp).2
    rw [hpos] at hh
    exact_mod_cast hh
  have hn1 : ∑ v, neg v ≤ 1 := by omega
  have htotal : ∑ v, f v = (∑ v, pos v) + ∑ v, neg v := by
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
  have htotal_pos : 0 < ∑ v, f v := by
    obtain ⟨v, hv⟩ := hne
    exact (Nat.pos_of_ne_zero hv).trans_le
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v))
  have htotal_two : ∑ v, f v = 2 := by omega
  have hsmall (v : V) : f v = 0 ∨ f v = 1 := by
    have hpv := Finset.single_le_sum (f := pos) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ v)
    have hnv := Finset.single_le_sum (f := neg) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ v)
    rcases hε v with hv | hv
    · have hvp : pos v = f v := by simp [pos, hv]
      omega
    · have hvn : neg v = f v := by simp [neg, hv]
      omega
  calc
    ∑ v, f v ^ 2 = ∑ v, f v := Finset.sum_congr rfl fun v _ => by
      rcases hsmall v with hv | hv <;> simp [hv]
    _ = 2 := htotal_two

variable {p : ℕ} {G : Type*} [Group G] [Finite G]
    {K : Type*} [Field K] {m n : ℕ}
    {d : PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K}
    {L : CyclicRootLift K m} {P : Sylow p G}

/-- The terminal restriction argument, with the three source-theory obligations
explicit: nonzero singular-vanishing columns, unit row differences, and
Thompson's bound for actual subcharacters. This is not the cyclic theorem. -/
theorem column_squares_of_restriction_theorems (a : Decomposition d residue L n)
    (q : LocalCharacterPair p P)
    (hnonzero : ∀ e, ∃ v, a.multiplicity v e ≠ 0)
    (hsingular : ∀ e g, p ∣ orderOf g →
      ordinarySum d (fun v => a.multiplicity v e) (ConjClasses.mk g) = 0)
    (hsigns : ∀ v, q.rowDifference d v = 1 ∨ q.rowDifference d v = -1)
    (hthompson : ∀ e, q.ThompsonBound
      (fun g => ordinarySum d (fun v => a.multiplicity v e) (ConjClasses.mk g))) :
    ∀ e : Fin n, ∑ v : {i // i ∈ d.block}, a.multiplicity v e ^ 2 = 2 := by
  intro e
  apply sum_sq_eq_two_of_signed_subsums (fun v => a.multiplicity v e)
    (q.rowDifference d) hsigns (hnonzero e)
    (q.ordinarySum_pairing_eq_zero d _ (hsingular e))
  intro c hc
  obtain ⟨ψ, hψ, hsum⟩ := ordinarySum_subcharacter d (fun v => a.multiplicity v e) c hc
  obtain ⟨z, hz, hlo, hhi⟩ := hthompson e
    (fun g => ordinarySum d c (ConjClasses.mk g)) ψ (ordinarySum_isCharacter d c) hψ hsum
  rw [q.ordinarySum_pairing] at hz
  have heq : (∑ v, (c v : ℤ) * q.rowDifference d v) = z := Int.cast_injective hz
  rw [heq]
  exact ⟨hlo, hhi⟩

/-- Apply the endpoint extraction to the exact supplied module columns.
The source-theory premises are the same unresolved ones as in the preceding
theorem; neither endpoints nor incidence are inputs. -/
theorem column_endpoints_of_restriction_theorems (a : Decomposition d residue L n)
    (q : LocalCharacterPair p P)
    (hnonzero : ∀ e, ∃ v, a.multiplicity v e ≠ 0)
    (hsingular : ∀ e g, p ∣ orderOf g →
      ordinarySum d (fun v => a.multiplicity v e) (ConjClasses.mk g) = 0)
    (hsigns : ∀ v, q.rowDifference d v = 1 ∨ q.rowDifference d v = -1)
    (hthompson : ∀ e, q.ThompsonBound
      (fun g => ordinarySum d (fun v => a.multiplicity v e) (ConjClasses.mk g))) :
    ∀ e : Fin n, ∃ l r : {i // i ∈ d.block}, l ≠ r ∧
      ∀ v, a.multiplicity v e = if v = l ∨ v = r then 1 else 0 := by
  intro e
  obtain ⟨l, r, hlr, hmul⟩ := exists_endpoints_of_sum_sq_eq_two (fun v => a.multiplicity v e)
    (column_squares_of_restriction_theorems a q hnonzero hsingular hsigns hthompson e)
  refine ⟨l, r, hlr, fun v => ?_⟩
  by_cases hv : v = l ∨ v = r
  · simpa only [if_pos hv] using hmul v
  · simpa only [if_neg hv] using hmul v

/-- Apply the restriction argument after identifying the actual supplied
projectives and their ordinary lifts. The independent source producers must
still provide the local signs, Thompson bound, and singular vanishing. -/
theorem column_squares_of_principal_columns (a : Decomposition d residue L n)
    (A : ∀ e, PrincipalColumn a e) (q : LocalCharacterPair p P)
    (hsingular : ∀ e g, p ∣ orderOf g → (A e).lift.complexRep.character g = 0)
    (hsigns : ∀ v, q.rowDifference d v = 1 ∨ q.rowDifference d v = -1)
    (hthompson : ∀ e, q.ThompsonBound
      (fun g => ordinarySum d (fun v => a.multiplicity v e) (ConjClasses.mk g))) :
    ∀ e : Fin n, ∑ v : {i // i ∈ d.block}, a.multiplicity v e ^ 2 = 2 := by
  apply column_squares_of_restriction_theorems a q (fun e => (A e).exists_nonzero a)
    _ hsigns hthompson
  intro e g hg
  rw [← (A e).ordinary_eq g]
  exact hsingular e g hg

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.ColumnNorms
