module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.ExceptionalFixed
public import Theory.ElementaryAbelian.Basic

/-!
# Cubic planes cannot centralize involutions of Aut(A₆)

The outer automorphism group of A₆ has order four, so an elementary
nine-group acts by inner automorphisms. Commutation with an involution
then embeds this same nine-group in its fixed subgroup in A₆. The three
actual fixed-group possibilities have orders 8, 24 and 10, none divisible
by nine. No specified inner or outer class is assumed.

Source: GLS3 5.2.7 and the fixed-group geometry of A₆; Aschbacher--Smith,
proof of 12.6.26, printed p.832, the faithful rank-two exclusion.
-/

public section
open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal

/-- No elementary nine-group acts faithfully while centralizing an involution of Aut(A₆). -/
theorem no_faithful_nine_centralizing_involution
    {P : Type*} [Group P] [Finite P] [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 9) (f : P →* AutA6) (hf : Function.Injective f)
    (b : AutA6) (hb : orderOf b = 2) (hcomm : ∀ x, f x * b = b * f x) : False := by
  let q := QuotientGroup.mk' inner
  have hQ : Nat.card (AutA6 ⧸ inner) = 4 := by rw [←index_eq_card,inner_index]
  have hfi (x : P) : f x ∈ inner := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 4)
    · apply orderOf_dvd_of_pow_eq_one
      change q (f x) ^ 3 = 1
      rw [←map_pow,←map_pow,Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 P) x,map_one,map_one]
    · rw [←hQ]
      exact orderOf_dvd_natCard (q (f x))
  let g : P →* A6 := innerEquiv.symm.toMonoidHom.comp (f.codRestrict inner hfi)
  have hg (x : P) : MulAut.conj (g x) = f x :=
    congrArg Subtype.val (innerEquiv.apply_symm_apply ⟨f x,hfi x⟩)
  have hfix (x : P) : b (g x) = g x := by
    apply inner_injective
    rw [←aut_conj_inner,hg,←hcomm x,mul_inv_cancel_right]
  let j : P →* automorphismFixedSubgroup b := g.codRestrict _ hfix
  have hj : Function.Injective j := by
    intro x y he
    apply hf
    rw [←hg x,←hg y]
    exact congrArg MulAut.conj (congrArg Subtype.val he)
  have hd := card_dvd_of_injective j hj
  rw [hP] at hd
  by_cases hi : b ∈ inner
  · obtain ⟨a,ha⟩ := hi
    change MulAut.conj a = b at ha
    have hao : orderOf a = 2 := by
      rw [←ha,orderOf_injective MulAut.conj inner_injective] at hb
      exact hb
    rw [←ha,inner_involution_fixed_card a hao] at hd
    norm_num at hd
  · by_cases hn : b ∈ natural
    · obtain ⟨e⟩ := natural_outer_involution_fixed_equiv_symmetricFour b hb hn hi
      rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm] at hd
      norm_num [Nat.factorial] at hd
    · rw [outside_natural_involution_fixed_card b hb hn] at hd
      norm_num at hd

end AlternatingSix.ShadowLocal
