module

public import Theory.SpecificGroups.PSL3Two.InvolutionResidual
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterCentralizerQuotient
public import Theory.GroupAction.FixedResidualFixerTransport

/-!
# Pointwise fixers of alternating four-subgroups of PSL₃(2)

The outer quotient and the centralizer of an involution are two-groups, so
the pointwise fixer of a subgroup of order twelve is a two-group. An inner
involution in this fixer would put that subgroup inside a two-group. An outer
involution has full automorphism centralizer of order twelve; the twelve inner
automorphisms supplied by the subgroup exhaust it, contradicting outerness.
Thus the fixer is trivial, independently of the embedding of A₄.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, proof of 13.9.1, printed p.974,
the terminal PSL₃(2) centralizer inspection.
-/

public section
namespace Matrix.PSL3Two
open Subgroup

private theorem sl_fixer_two (U : Subgroup SL) (t : U) (ht : orderOf (t : SL) = 2) :
    IsPGroup 2 (fixingSubgroup (MulAut SL) (U : Set SL)) := by
  let F := fixingSubgroup (MulAut SL) (U : Set SL)
  intro α
  obtain ⟨j, hj⟩ := Automorphisms.outer_sl_isTwoGroup
    (QuotientGroup.mk' (MulAut.innerSubgroup SL) (α : MulAut SL))
  have hi : (α : MulAut SL) ^ (2 ^ j) ∈ MulAut.innerSubgroup SL := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (MulAut.innerSubgroup SL) (α : MulAut SL)) ^ (2 ^ j) = 1 at hj
    rw [← map_pow] at hj
    exact hj
  obtain ⟨g, hg⟩ := hi
  have hf : ((α : MulAut SL) ^ (2 ^ j)) (t : SL) = t :=
    (mem_fixingSubgroup_iff _).mp (F.pow_mem α.property _) t t.property
  rw [← hg, MulAut.conj_apply] at hf
  have hgC : g ∈ centralizer ({(t : SL)} : Set SL) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hf)
  obtain ⟨k, hk⟩ := InvolutionResidual.sl_centralizer_two t ht ⟨g, hgC⟩
  have hk' : g ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  refine ⟨j + k, Subtype.ext ?_⟩
  change (α : MulAut SL) ^ (2 ^ (j + k)) = 1
  rw [pow_add, pow_mul, ← hg, ← map_pow, hk', map_one]

private theorem not_two_of_card_twelve {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H = 12) (hp : IsPGroup 2 H) : False := by
  obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
  rw [hcard] at hn
  have h3 : 3 ∣ 2 ^ n := (by decide : 3 ∣ 12).trans hn
  have := Nat.prime_three.dvd_of_dvd_pow h3
  norm_num at this

private theorem sl_fixer_eq_bot_of_card_twelve (U : Subgroup SL) (hcard : Nat.card U = 12) :
    fixingSubgroup (MulAut SL) (U : Set SL) = ⊥ := by
  let F := fixingSubgroup (MulAut SL) (U : Set SL)
  have hconj : Function.Injective (MulAut.conj : SL →* MulAut SL) :=
    MulAut.conj_injective_of_center_eq_bot center_eq_bot
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by rw [hcard]; decide)
  have ht' : orderOf (t : SL) = 2 :=
    (orderOf_injective U.subtype U.subtype_injective t).trans ht
  have hp := sl_fixer_two U t ht'
  by_contra hne
  have : Nontrivial F := (Subgroup.nontrivial_iff_ne_bot F).mpr hne
  obtain ⟨n, hn, hcF⟩ := hp.nontrivial_iff_card.mp inferInstance
  obtain ⟨β, hβ⟩ := exists_prime_orderOf_dvd_card' (G := F) 2
    (hcF.symm ▸ dvd_pow_self 2 (by omega : n ≠ 0))
  have hβ' : orderOf (β : MulAut SL) = 2 :=
    (orderOf_injective F.subtype F.subtype_injective β).trans hβ
  have hβ2 : (β : MulAut SL) ^ 2 = 1 := by
    simpa only [hβ'] using (pow_orderOf_eq_one (β : MulAut SL))
  have hf (u : U) : (β : MulAut SL) u = u :=
    (mem_fixingSubgroup_iff _).mp β.property u u.property
  by_cases hi : (β : MulAut SL) ∈ MulAut.innerSubgroup SL
  · obtain ⟨g, hg⟩ := hi
    have hg2 : g ^ 2 = 1 := hconj (by rw [map_pow, hg, hβ2, map_one])
    have hgne : g ≠ 1 := by
      intro he
      rw [he, map_one] at hg
      rw [← hg, orderOf_one] at hβ'
      contradiction
    let f : U →* centralizer ({g} : Set SL) := U.subtype.codRestrict _ (by
      intro u
      apply mem_centralizer_singleton_iff.mpr
      have hh := hf u
      rw [← hg, MulAut.conj_apply] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm)
    exact not_two_of_card_twelve hcard
      ((InvolutionResidual.sl_centralizer_two g (orderOf_eq_prime hg2 hgne)).of_injective f
        (fun a b hh => Subtype.ext
          (congrArg (fun z : centralizer ({g} : Set SL) => (z : SL)) hh)))
  · obtain ⟨π, hπ, hk⟩ :=
      Automorphisms.OuterCentralizerQuotient.exists_outer_centralizer_symmetricThree_quotient
        β hβ2 hi
    let C := centralizer ({(β : MulAut SL)} : Set (MulAut SL))
    have hc : Nat.card C = 12 := by
      have hh := π.ker.card_mul_index
      rw [hk, index_ker, MonoidHom.range_eq_top.mpr hπ, card_top] at hh
      have hs : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm]
        decide
      rw [hs] at hh
      exact hh.symm
    let f : U →* C := ((MulAut.conj : SL →* MulAut SL).comp U.subtype).codRestrict _ (by
      intro u
      apply mem_centralizer_singleton_iff.mpr
      apply MulEquiv.ext
      intro x
      change (u : SL) * ((β : MulAut SL) x) * (u : SL)⁻¹ =
        (β : MulAut SL) ((u : SL) * x * (u : SL)⁻¹)
      rw [map_mul, map_mul, map_inv, hf])
    have hfi : Function.Injective f := fun a b hh =>
      Subtype.ext (hconj (congrArg Subtype.val hh))
    have hfs : Function.Surjective f :=
      ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi, hcard.trans hc.symm⟩).2
    obtain ⟨u, hu⟩ := hfs ⟨β, mem_centralizer_singleton_iff.mpr rfl⟩
    exact hi ⟨u, congrArg Subtype.val hu⟩

/-- The full pointwise automorphism fixer of any actual A₄ subgroup of PSL₃(2) is trivial. -/
theorem alternatingFour_fixer_eq_bot (U : Subgroup PSL)
    (eU : U ≃* alternatingGroup (Fin 4)) :
    fixingSubgroup (MulAut PSL) (U : Set PSL) = ⊥ := by
  let V := U.map equiv.symm.toMonoidHom
  have hc : Nat.card V = 12 := by
    rw [card_map_of_injective equiv.symm.injective, Nat.card_congr eU.toEquiv,
      Nat.card_eq_fintype_card]
    decide
  have h := sl_fixer_eq_bot_of_card_twelve V hc
  rw [← MulAut.map_fixer equiv.symm U] at h
  exact (map_eq_bot_iff_of_injective _ (MulAut.congr equiv.symm).injective).mp h

end Matrix.PSL3Two
