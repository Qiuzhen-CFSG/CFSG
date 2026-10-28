module

public import Theory.SpecificGroups.SymmetricFive.EvenInvolutionCentralizer
public import Theory.SpecificGroups.SymmetricFiveInvolutions
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.Sylow

/-!
# Involutions centralizing a full Sylow two-subgroup of S5

An odd involution is a transposition, whose centralizer has order twelve and
cannot contain a Sylow two-subgroup of order eight. Thus a Sylow-centralizing
involution is even, with centralizer of order eight. Every two-perfect group
mapping into this centralizer has trivial image.

Source application: Aschbacher--Smith, 14.3.31, printed p.1003. The shifted
actor centralizes the marked plane stabilizer, including the actual Sylow
and the point residual; the latter has nontrivial two-perfect image.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricFive

/-- An involution centralizing a full Sylow two-subgroup has a two-group centralizer. -/
theorem involution_centralizer_isTwoGroup_of_sylow
    (P : Sylow 2 (Equiv.Perm (Fin 5))) (a : Equiv.Perm (Fin 5))
    (ha : orderOf a = 2)
    (hP : (P : Subgroup _) ≤ centralizer ({a} : Set _)) :
    IsPGroup 2 (centralizer ({a} : Set _)) := by
  have he : a ∈ alternatingGroup (Fin 5) := by
    by_contra hn
    have hs := Equiv.Perm.five_isSwap_of_outer_involution a ha hn
    have hc : Nat.card (centralizer ({a} : Set (Equiv.Perm (Fin 5)))) = 12 := by
      rw [Equiv.Perm.nat_card_centralizer, Equiv.Perm.isSwap_iff_cycleType.mp hs]
      norm_num
    have h8 : Nat.card P = 8 := by
      rw [P.card_eq_multiplicity, Nat.card_eq_fintype_card, Fintype.card_perm]
      decide +kernel
    have hd := card_dvd_of_le hP
    rw [h8, hc] at hd
    norm_num at hd
  exact IsPGroup.of_card (n := 3) (Equiv.Perm.even_involution_five_centralizer_card a ha he)

/-- Such an involution cannot commute with a nontrivial two-perfect image. -/
theorem twoPerfect_image_eq_one_of_commute {J : Type*} [Group J]
    (P : Sylow 2 (Equiv.Perm (Fin 5))) (a : Equiv.Perm (Fin 5))
    (ha : orderOf a = 2)
    (hP : (P : Subgroup _) ≤ centralizer ({a} : Set _))
    (f : J →* Equiv.Perm (Fin 5)) (hp : IsPPerfect 2 J)
    (hc : ∀ j, Commute a (f j)) : f = 1 := by
  let g := f.codRestrict (centralizer ({a} : Set _))
    (fun j => mem_centralizer_singleton_iff.mpr (hc j).symm.eq)
  have he := hp.hom_eq_one_of_isPGroup
    (involution_centralizer_isTwoGroup_of_sylow P a ha hP) g
  apply MonoidHom.ext
  intro j
  exact congrArg Subtype.val (congrArg (fun f => f j) he)

end Theory.SpecificGroups.SymmetricFive
