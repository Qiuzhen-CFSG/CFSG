module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Text
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.Tests
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeChecks.Tables

/-!
# Sound point-orbit tests for Held representatives

Words in the four marked generators and a representative belong to their
actual generated subgroup. A nontrivial prime-length orbit of a power of
such a word forces the prime to divide its order. Taking a suitable power
then supplies an actual element of that prime order in the same subgroup.
No full permutation power identity or subgroup catalogue is assumed.

The evaluators are proved equal to the faithful Held representation. They
use the unchanged signed words and the ATLAS letter-order convention from
`../source/README.md`. Concrete orbit certificates are separate inputs.
-/

@[expose] public section
namespace Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

def wordAction {α : Type*} (x xi y yi : α → α) : List (Bool × ℤ) → α → α
  | [], t => t
  | (b, Int.ofNat n) :: w, t => (if b then y else x)^[n] (wordAction x xi y yi w t)
  | (b, Int.negSucc n) :: w, t => (if b then yi else xi)^[n+1] (wordAction x xi y yi w t)

theorem wordAction_eq {α : Type*} (x y : Equiv.Perm α)
    (w : List (Bool × ℤ)) (t : α) :
    wordAction x (x⁻¹ : Equiv.Perm α) y (y⁻¹ : Equiv.Perm α) w t = wordEval x y w t := by
  induction w generalizing t with
  | nil => rfl
  | cons v w ih =>
    rcases v with ⟨b, n⟩
    cases b <;> cases n <;>
      simp only [wordAction, wordEval, Bool.false_eq_true, if_false, if_true,
        Int.ofNat_eq_natCast, zpow_natCast, zpow_negSucc, ← inv_pow,
        Equiv.Perm.mul_apply, Equiv.Perm.coe_pow, ih]

def representativeAction (j : Fin 4831) : Fin 2058 → Fin 2058 :=
  wordAction (packedAction packA) (packedAction packA) (packedAction packB) (packedAction packBi) (decodeWord (representativeText j))

theorem representativeAction_eq (j : Fin 4831) :
    representativeAction j = representation (representative j) := by
  funext t
  rw [representative, map_wordEval, representativeWord_eq_decodeText]
  change wordAction fastA (fastA⁻¹ : Equiv.Perm (Fin 2058)) fastB
    (fastB⁻¹ : Equiv.Perm (Fin 2058)) _ t = _
  rw [wordAction_eq, fastA_eq, fastB_eq]
  rfl

def localPerm (b : Bool) : Equiv.Perm (Fin 2058) :=
  ((fastA * fastB ^ 5) * (fastA * fastB ^ (if b then 2 else 3))) *
    ((fastA * fastB ^ 4) * (fastA * fastB ^ 6))

def markedAction (i : Fin 4) : Fin 2058 → Fin 2058 :=
  wordAction (packedAction packA) (packedAction packA) (localPerm false)
    ((localPerm false)⁻¹ : Equiv.Perm (Fin 2058)) (generatorWords i)

theorem markedAction_eq (i : Fin 4) : markedAction i = representation (markedGenerator i) := by
  funext t
  rw [markedGenerator, map_wordEval, representation_localWord]
  change wordAction fastA (fastA⁻¹ : Equiv.Perm (Fin 2058)) (localPerm false)
    ((localPerm false)⁻¹ : Equiv.Perm (Fin 2058)) _ t = _
  rw [wordAction_eq, localPerm, fastA_eq, fastB_eq]
  rfl

def testLetter (r : He) : ℕ → He
  | 1 => markedGenerator 0
  | 2 => markedGenerator 1
  | 3 => markedGenerator 2
  | 4 => markedGenerator 3
  | _ => r

def testLetterAction (j : Fin 4831) : ℕ → Fin 2058 → Fin 2058
  | 1 => markedAction 0
  | 2 => markedAction 1
  | 3 => markedAction 2
  | 4 => markedAction 3
  | _ => representativeAction j

theorem testLetterAction_eq (j : Fin 4831) (i : ℕ) :
    testLetterAction j i = representation (testLetter (representative j) i) := by
  unfold testLetterAction testLetter
  split
  · exact markedAction_eq 0
  · exact markedAction_eq 1
  · exact markedAction_eq 2
  · exact markedAction_eq 3
  · exact representativeAction_eq j

def testWord (r : He) : List ℕ → He
  | [] => 1
  | i :: w => testLetter r i * testWord r w

def testAction (j : Fin 4831) : List ℕ → Fin 2058 → Fin 2058
  | [], t => t
  | i :: w, t => testLetterAction j i (testAction j w t)

theorem testAction_eq (j : Fin 4831) (w : List ℕ) :
    testAction j w = representation (testWord (representative j) w) := by
  funext t
  induction w generalizing t with
  | nil => rfl
  | cons i w ih =>
    simp only [testAction, testWord, map_mul, Equiv.Perm.mul_apply,
      testLetterAction_eq, ih]

theorem testWord_mem (r : He) (w : List ℕ) :
    testWord r w ∈ markedSubgroup ⊔ Subgroup.zpowers r := by
  have hletter (i : ℕ) : testLetter r i ∈ markedSubgroup ⊔ Subgroup.zpowers r := by
    unfold testLetter
    split
    · exact Subgroup.mem_sup_left (markedGenerator_mem 0)
    · exact Subgroup.mem_sup_left (markedGenerator_mem 1)
    · exact Subgroup.mem_sup_left (markedGenerator_mem 2)
    · exact Subgroup.mem_sup_left (markedGenerator_mem 3)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih => exact Subgroup.mul_mem _ (hletter i) ih

theorem hasPrimeObstruction_of_orbit (r x : He) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hx : x ∈ markedSubgroup ⊔ Subgroup.zpowers r) (i : Fin 2058)
    (hper : (representation x ^ p) i = i) (hne : representation x i ≠ i) :
    HasPrimeObstruction r := by
  let : Fact p.Prime := ⟨hp⟩
  have hmin : Function.minimalPeriod (representation x) i = p :=
    Function.minimalPeriod_eq_prime
      (by simpa only [Function.IsPeriodicPt, Function.IsFixedPt, Equiv.Perm.coe_pow] using hper) hne
  have hdvd : p ∣ orderOf x := by
    rw [← hmin]
    apply Function.IsPeriodicPt.minimalPeriod_dvd
    change (representation x)^[orderOf x] i = i
    rw [← Equiv.Perm.coe_pow, ← map_pow, pow_orderOf_eq_one, map_one]
    rfl
  exact ⟨p, hp, hp2, hp3, x ^ (orderOf x / p),
    Subgroup.pow_mem _ hx _, orderOf_pow_orderOf_div (orderOf_pos x).ne' hdvd⟩

theorem obstruction_of_testAction (j : Fin 4831) (w : List ℕ) (p e : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (i : Fin 2058)
    (hper : (testAction j w)^[e * p] i = i)
    (hne : (testAction j w)^[e] i ≠ i) : HasPrimeObstruction (representative j) := by
  apply hasPrimeObstruction_of_orbit (representative j)
    (testWord (representative j) w ^ e) p hp hp2 hp3
    (Subgroup.pow_mem _ (testWord_mem _ _) _) i
  · simpa only [map_pow, Equiv.Perm.coe_pow, ← Function.iterate_mul,
      testAction_eq] using hper
  · simpa only [map_pow, Equiv.Perm.coe_pow, testAction_eq] using hne


end Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
