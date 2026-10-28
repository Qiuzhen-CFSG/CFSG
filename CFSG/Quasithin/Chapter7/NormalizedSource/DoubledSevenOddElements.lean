module
public import CFSG.Quasithin.ChapterH.Section05To09.AlternatingPair
public import Theory.Representation.AlternatingSevenConjugatePair.SourceLineGeometry.Basic

/-!
# Odd prime elements in a small-codimension A₇ centralizer

On the actual H.8 conjugate pair, prime-degree bounds exclude elements of
orders five and seven from centralizers of subspaces of corank below six.
A single three-cycle fixes nothing. Thus any odd prime-order element of
such a centralizer is a double three-cycle. The chosen-orbit application
is in NonFFSourceDoubledSevenMixed.

Source: Aschbacher--Smith, 7.5.5, p.701 and H.8.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open Representation.AlternatingSevenConjugatePair
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem doubledSeven_small_odd_prime (D : Pair V) (s : Equiv.Perm (Fin 7))
    (hp : (orderOf s).Prime) (ho : orderOf s ≠ 2)
    (hc : fixedCodim D.representation (zpowers s) < 6) :
    orderOf s = 3 ∧ s.cycleType = {3,3} := by
  classical
  have hsd : orderOf s ∣ Nat.factorial 7 := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] using orderOf_dvd_natCard s
  have hle : orderOf s ≤ 7 := hp.dvd_factorial.mp hsd
  have hcases : orderOf s = 3 ∨ orderOf s = 5 ∨ orderOf s = 7 := by
    have hlo := hp.two_le
    have hn4 : orderOf s ≠ 4 := fun he => (by decide : ¬ Nat.Prime 4) (he ▸ hp)
    have hn6 : orderOf s ≠ 6 := fun he => (by decide : ¬ Nat.Prime 6) (he ▸ hp)
    omega
  have heven : s ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    rcases Int.units_eq_one_or s.sign with hs | hs
    · exact hs
    · have hd := orderOf_map_dvd Equiv.Perm.sign s
      rw [hs,show orderOf (-1 : ℤˣ) = 2 from orderOf_eq_prime (by decide) (by decide)] at hd
      exact (ho (((Nat.dvd_prime hp).mp hd).resolve_left (by decide)).symm).elim
  let a : alternatingGroup (Fin 7) := ⟨s,heven⟩
  have ha : orderOf a = orderOf s := (Subgroup.orderOf_coe a).symm
  have hsum := D.inner_fixedCodim a
  change fixedCodim D.representation (zpowers s) = _ at hsum
  have h3 : orderOf s = 3 := by
    rcases hcases with hh | hh | hh
    · exact hh
    · have h1 := prime_order_le_fixedCodim D.first.toRepresentation D.first_faithful
        (by decide : Nat.Prime 5) (by decide) a (ha.trans hh)
      have h2 := prime_order_le_fixedCodim D.second.toRepresentation D.second_faithful
        (by decide : Nat.Prime 5) (by decide) a (ha.trans hh)
      rw [BinaryPrimeDegree.orderOf_two_mod_five] at h1 h2
      omega
    · have h1 := prime_order_le_fixedCodim D.first.toRepresentation D.first_faithful
        (by decide : Nat.Prime 7) (by decide) a (ha.trans hh)
      have h2 := prime_order_le_fixedCodim D.second.toRepresentation D.second_faithful
        (by decide : Nat.Prime 7) (by decide) a (ha.trans hh)
      rw [BinaryPrimeDegree.orderOf_two_mod_seven] at h1 h2
      omega
  refine ⟨h3,?_⟩
  obtain ⟨n,hn⟩ := Equiv.Perm.cycleType_prime_order hp
  have hs := s.sum_cycleType_le
  rw [hn,h3,Multiset.sum_replicate,nsmul_eq_mul] at hs
  have hn01 : n = 0 ∨ n = 1 := by norm_num at hs; omega
  rcases hn01 with rfl | rfl
  · have ht : s.IsThreeCycle := by change s.cycleType = {3}; simpa [h3] using hn
    have hf : fixedSpace D.representation (zpowers s) = ⊥ := by
      apply bot_unique
      intro v hv
      exact SourceLineGeometry.threeCycle_fixedPointFree D s ht v
        ((mem_fixedSpace_zpowers_iff _ _ _).mp hv)
    have hh := fixedCodim_add_finrank D.representation (zpowers s)
    rw [hf,finrank_bot,D.finrank_eq_eight] at hh
    omega
  · simpa [h3] using hn

end CFSG.Quasithin.Chapter7.NormalizedSource
