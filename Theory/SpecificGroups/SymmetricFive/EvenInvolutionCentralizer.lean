module
public import Theory.SpecificGroups.SymmetricFive.EvenInvolutions
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Tactic
/-!
# Cubic actors move every even involution of S₅

The centralizer order follows directly from the double-transposition cycle
type. Its order is eight, so it contains no element of order three. In the
source application, a genuine cubic transporter in the second parabolic
therefore separates the two involution images in the original S₅ quotient.

Source: Aschbacher–Smith J.4.7, printed p.444.
-/

public section
namespace Equiv.Perm
open Subgroup

theorem even_involution_five_centralizer_card (a:Equiv.Perm (Fin 5))
    (ha:orderOf a=2) (he:a∈alternatingGroup (Fin 5)) :
    Nat.card (centralizer ({a}:Set (Equiv.Perm (Fin 5))))=8 := by
  have hh:=orderOf_eq_prime_iff.mp ha
  rw [nat_card_centralizer,even_involution_five_cycleType a he hh.1 hh.2]
  norm_num


theorem three_not_commute_even_involution_five (a b:Equiv.Perm (Fin 5))
    (ha:orderOf a=2) (he:a∈alternatingGroup (Fin 5)) (hb:orderOf b=3) :
    ¬Commute a b := by
  intro hc
  have hmem:b∈centralizer ({a}:Set (Equiv.Perm (Fin 5))) :=
    mem_centralizer_singleton_iff.mpr hc.symm.eq
  have hd:=orderOf_dvd_natCard (⟨b,hmem⟩:centralizer ({a}:Set (Equiv.Perm (Fin 5))))
  rw [←orderOf_coe,hb,even_involution_five_centralizer_card a ha he] at hd
  contradiction

theorem three_conjugates_even_involution_five (a b:Equiv.Perm (Fin 5))
    (ha:orderOf a=2) (he:a∈alternatingGroup (Fin 5)) (hb:orderOf b=3) :
    b*a*b⁻¹≠a := by
  intro h
  apply three_not_commute_even_involution_five a b ha he hb
  apply Commute.symm
  show b*a=a*b
  calc
    b*a=(b*a*b⁻¹)*b := by group
    _=a*b := by rw [h]

end Equiv.Perm
