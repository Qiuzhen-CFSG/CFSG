module

public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Logic.Equiv.Fintype

/-!
# Rank-two proper overgroups of two-three subgroups on seven letters

A subgroup of S₇ whose order is divisible by neither five nor seven has
an odd orbit of length one or three. Its setwise stabilizer is proper even
on A₇. In either case the stabilizer contains two independent three-cycles:
(0 1 2) and (3 4 5), after transporting the distinguished subset from
{6} or {0,1,2}. Their actual injective C₃ × C₃ action witnesses three-rank
two in the even part of the stabilizer.

Only calculations on nine elements and seven points use kernel evaluation;
no subgroup catalogue or covering assumption is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the first
paragraph of the proof of 15.3.28, printed p.1131 (PDF p.1148).
-/

public section

open Subgroup Equiv
open scoped BigOperators

namespace Theory.SpecificGroups.Alternating.SevenPartitionOvergroups

/-- The actual setwise stabilizer, expressed by preservation of membership. -/
def stabilizer (s : Set (Fin 7)) : Subgroup (Equiv.Perm (Fin 7)) where
  carrier := {g | ∀ x, g x ∈ s ↔ x ∈ s}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {g h} hg hh x => (hg (h x)).trans (hh x)
  inv_mem' := by
    intro g hg x
    simpa using (hg (g⁻¹ x)).symm

/-- A subgroup with neither five nor seven in its order has an invariant singleton or triple. -/
theorem small_orbit (B : Subgroup (Equiv.Perm (Fin 7))) (h5 : ¬ 5 ∣ Nat.card B)
    (h7 : ¬ 7 ∣ Nat.card B) :
    ∃ s : Set (Fin 7), (Nat.card s = 1 ∨ Nat.card s = 3) ∧ B ≤ stabilizer s := by
  classical
  let Q := MulAction.orbitRel.Quotient B (Fin 7)
  let : Fintype Q := Fintype.ofFinite Q
  have hsum : (∑ q : Q, Nat.card q.orbit) = 7 := by
    simpa only [Nat.card_sigma, Nat.card_fin] using
      (Nat.card_congr (MulAction.selfEquivSigmaOrbits' B (Fin 7))).symm
  have hex : ∃ q : Q, ¬ 2 ∣ Nat.card q.orbit := by
    by_contra hn
    push Not at hn
    have hd := Finset.dvd_sum (fun q (_ : q ∈ Finset.univ) => hn q)
    rw [hsum] at hd
    norm_num at hd
  obtain ⟨q, hq⟩ := hex
  have hb : Nat.card q.orbit ≤ 7 := by
    simpa only [Nat.card_fin] using
      (Nat.card_le_card_of_injective (fun x : q.orbit => x.val) Subtype.val_injective)
  have hd : Nat.card q.orbit ∣ Nat.card B := by
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer B q.out)]
    exact card_quotient_dvd_card _
  have hc : Nat.card q.orbit = 1 ∨ Nat.card q.orbit = 3 := by
    have hn5 : Nat.card q.orbit ≠ 5 := fun h => h5 (by rwa [h] at hd)
    have hn7 : Nat.card q.orbit ≠ 7 := fun h => h7 (by rwa [h] at hd)
    omega
  refine ⟨q.orbit, hc, ?_⟩
  intro g hg x
  constructor
  · intro hx
    have hh := q.mapsTo_smul_orbit (⟨g⁻¹, B.inv_mem hg⟩ : B) hx
    simpa using hh
  · intro hx
    exact q.mapsTo_smul_orbit (⟨g, hg⟩ : B) hx

private abbrev E := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)
private def perm (a : E) : (Equiv.Perm (Fin 7)) :=
  (swap 0 1 * swap 1 2) ^ a.1.toAdd.val * (swap 3 4 * swap 4 5) ^ a.2.toAdd.val

private def embedding : E →* (Equiv.Perm (Fin 7)) where
  toFun := perm
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem embedding_injective : Function.Injective embedding := by decide +kernel

private def block (t : Bool) : Set (Fin 7) := {x | if t then x = 0 ∨ x = 1 ∨ x = 2 else x = 6}

private instance (t : Bool) : DecidablePred (· ∈ block t) := by
  intro x
  change Decidable (if t then x = 0 ∨ x = 1 ∨ x = 2 else x = 6)
  infer_instance

private theorem embedding_block (t : Bool) (a : E) : embedding a ∈ stabilizer (block t) := by
  change ∀ x, embedding a x ∈ block t ↔ x ∈ block t
  revert t a
  decide +kernel

private theorem embedding_even (a : E) : embedding a ∈ (alternatingGroup (Fin 7)) := by
  change (embedding a).sign = 1
  revert a
  decide +kernel

private def moving : (Equiv.Perm (Fin 7)) := swap 0 3 * swap 3 6

private theorem moving_even : moving ∈ (alternatingGroup (Fin 7)) := by
  change moving.sign = 1
  decide +kernel

private theorem moving_not_mem (t : Bool) : moving ∉ stabilizer (block t) := by
  change ¬ ∀ x, moving x ∈ block t ↔ x ∈ block t
  revert t
  decide +kernel

private theorem block_card (t : Bool) : Nat.card (block t) = if t then 3 else 1 := by
  cases t <;> rw [Nat.card_eq_fintype_card] <;> decide +kernel

private theorem elementary_cube (a : E) : a ^ 3 = 1 := by
  revert a
  decide +kernel

private theorem elementary_card : Nat.card E = 3 ^ 2 := by
  simp [E, Nat.card_eq_fintype_card]

/-- Both source stabilizers omit an even permutation and contain an elementary nine. -/
theorem stabilizer_obstruction (s : Set (Fin 7))
    (hs : Nat.card s = 1 ∨ Nat.card s = 3) :
    ¬ (alternatingGroup (Fin 7)) ≤ stabilizer s ∧ 2 ≤ primeRank 3 (stabilizer s ⊓ (alternatingGroup (Fin 7)) : Subgroup (Equiv.Perm (Fin 7))) := by
  classical
  obtain ⟨t, ht⟩ : ∃ t : Bool, Nat.card (block t) = Nat.card s := by
    rcases hs with h | h
    · exact ⟨false, by rw [block_card, h]; rfl⟩
    · exact ⟨true, by rw [block_card, h]; rfl⟩
  let e : block t ≃ s := Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using ht)
  let p : (Equiv.Perm (Fin 7)) := e.extendSubtype
  have hp (x : Fin 7) : p x ∈ s ↔ x ∈ block t := by
    constructor
    · intro hx
      by_contra hn
      exact e.extendSubtype_not_mem x hn hx
    · exact e.extendSubtype_mem x
  have htransport (g : (Equiv.Perm (Fin 7))) (hg : g ∈ stabilizer (block t)) :
      p * g * p⁻¹ ∈ stabilizer s := by
    intro x
    change p (g (p⁻¹ x)) ∈ s ↔ x ∈ s
    rw [hp, hg]
    simpa using (hp (p⁻¹ x)).symm
  constructor
  · intro hle
    have hm := hle ((inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem moving moving_even p)
    apply moving_not_mem t
    intro x
    have hh := hm (p x)
    simpa only [Perm.mul_apply, show p⁻¹ (p x) = x from p.symm_apply_apply x, hp] using hh
  · let f : E →* (stabilizer s ⊓ (alternatingGroup (Fin 7)) : Subgroup (Equiv.Perm (Fin 7))) :=
      ((MulAut.conj p).toMonoidHom.comp embedding).codRestrict _
        (fun a => ⟨htransport _ (embedding_block t a),
          (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem _ (embedding_even a) p⟩)
    apply primeRank_ge_of_elementary_embedding elementary_cube elementary_card f
    intro a b hab
    exact embedding_injective ((MulAut.conj p).injective (congrArg Subtype.val hab))

/-- The proper-overgroup obstruction in the actual seven-point permutation action. -/
theorem exists_overgroup (B : Subgroup (Equiv.Perm (Fin 7))) (h5 : ¬ 5 ∣ Nat.card B)
    (h7 : ¬ 7 ∣ Nat.card B) :
    ∃ K : Subgroup (Equiv.Perm (Fin 7)), B ≤ K ∧ ¬ (alternatingGroup (Fin 7)) ≤ K ∧ 2 ≤ primeRank 3 (K ⊓ (alternatingGroup (Fin 7)) : Subgroup (Equiv.Perm (Fin 7))) := by
  obtain ⟨s, hs, hB⟩ := small_orbit B h5 h7
  exact ⟨stabilizer s, hB, stabilizer_obstruction s hs⟩

end Theory.SpecificGroups.Alternating.SevenPartitionOvergroups
