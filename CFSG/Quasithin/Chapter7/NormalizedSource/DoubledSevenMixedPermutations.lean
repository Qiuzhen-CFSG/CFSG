module
public import Theory.Representation.AlternatingSevenConjugatePair.FixedFamily.Coordinates
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Permutation geometry for the doubled A₇ centralizer argument

Every even involution is conjugate to (01)(23). For this marking, if a
double three-cycle conjugates that involution to one commuting with
(02)(13), an odd transposition on the remaining three letters centralizes
the original involution and makes the product of the cubic with its
conjugate a single three-cycle. These are group identities, independent
of any choice of four-dimensional model.

The finite identity is checked after the standard first-letter
permutation decomposition, keeping each kernel computation bounded.
The actual full-pair consumer is DoubledSevenMixedGeometry.
Source: Aschbacher--Smith 7.5.5, printed p.701. This replaces the
insufficient isolated-plane centralizer assertion by a two-summand argument.
-/

public noncomputable section
open Subgroup Equiv
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open Representation.AlternatingSevenConjugatePair.FixedFamily
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry

theorem doubledSeven_even_involution_conjugate (t : S7)
    (ht : orderOf t = 2) (he : t ∈ alternatingGroup (Fin 7)) :
    ∃ g : S7, g * t * g⁻¹ = centralInvolution := by
  obtain ⟨n,hn⟩ := Perm.cycleType_prime_order (ht ▸ Nat.prime_two)
  have hb := t.sum_cycleType_le
  rw [hn,ht,Multiset.sum_replicate,nsmul_eq_mul] at hb
  have hnle : n ≤ 2 := by norm_num at hb; omega
  have hsign := Perm.sign_of_cycleType t
  rw [hn,ht,Multiset.sum_replicate,Multiset.card_replicate,nsmul_eq_mul] at hsign
  have he' : t.sign = 1 := he
  have hn1 : n = 1 := by
    interval_cases n
    · norm_num [he'] at hsign
      exact ((by decide : ¬ (1 : ℤˣ) = (-1)^3) hsign).elim
    · rfl
    · norm_num [he'] at hsign
      exact ((by decide : ¬ (1 : ℤˣ) = (-1)^9) hsign).elim
  apply isConj_iff.mp
  apply Perm.isConj_iff_cycleType_eq.mpr
  rw [hn,hn1,ht]
  decide

local instance : Fintype (Perm (Fin 6)) := fintypePerm
local instance (s : S7) : Decidable s.IsThreeCycle := inferInstanceAs (Decidable (s.cycleType = {3}))
private def Test (s : S7) : Prop := s * s * s = 1 → s ≠ 1 →
    crossSwap * (s * centralInvolution * s⁻¹) = (s * centralInvolution * s⁻¹) * crossSwap →
    s.IsThreeCycle ∨ (s * (swap 4 5 * s * swap 4 5)).IsThreeCycle ∨
    (s * (swap 4 6 * s * swap 4 6)).IsThreeCycle ∨
    (s * (swap 5 6 * s * swap 5 6)).IsThreeCycle
private instance (s : S7) : Decidable (Test s) := inferInstanceAs (Decidable (_ → _ → _ → _))
private theorem certificate (i : Fin 7) : ∀ p : Perm (Fin 6), Test (Perm.decomposeFin.symm (i,p)) := by
  fin_cases i <;> decide +kernel

private theorem full (s : S7) : Test s := by
  have hh := certificate (Perm.decomposeFin s).1 (Perm.decomposeFin s).2
  simpa only [Prod.mk.eta, Equiv.symm_apply_apply] using hh


/-- The odd transposition preserves the involution's fixed space and turns
this cubic and its conjugate into a single three-cycle. -/
theorem doubledSeven_mixed_transposition (s : S7) (hs : s.cycleType = {3,3})
    (hc : crossSwap * (s * centralInvolution * s⁻¹) =
      (s * centralInvolution * s⁻¹) * crossSwap) :
    ∃ g : S7, g ∉ alternatingGroup (Fin 7) ∧ g*g = 1 ∧
      centralInvolution*g = g*centralInvolution ∧ (s*(g*s*g)).IsThreeCycle := by
  have ho : orderOf s = 3 := by rw [← s.lcm_cycleType,hs]; decide
  have hcube : s*s*s = 1 := by simpa only [pow_succ,pow_zero,one_mul] using
    (show s ^ 3 = 1 from ho ▸ pow_orderOf_eq_one s)
  have hne : s ≠ 1 := by intro hh; simp only [hh,orderOf_one] at ho; omega
  rcases full s hcube hne hc with hthree | h45 | h46 | h56
  · change s.cycleType = {3} at hthree
    rw [hs] at hthree
    exact (by decide : ({3,3} : Multiset ℕ) ≠ {3}) hthree |>.elim
  · exact ⟨swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide, by decide, by decide, h45⟩
  · exact ⟨swap 4 6, by rw [Equiv.Perm.mem_alternatingGroup]; decide, by decide, by decide, h46⟩
  · exact ⟨swap 5 6, by rw [Equiv.Perm.mem_alternatingGroup]; decide, by decide, by decide, h56⟩

end CFSG.Quasithin.Chapter7.NormalizedSource

