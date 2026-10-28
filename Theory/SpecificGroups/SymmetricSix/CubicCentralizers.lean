module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Mathlib.GroupTheory.IndexNormal

/-!
# Two-perfect subgroups centralizing an involution in S₆

Let D be a subgroup of the actual six-point alternating group, of order
divisible by six and with no nontrivial two-group quotient. If an involution
of S₆ centralizes D, then D is isomorphic to A₄.

An even involution has fixed subgroup of order eight in A₆, contradicting
the factor three in |D|. The fixed subgroup of either type of odd involution
is S₄. In this four-point realization, two-perfection puts D inside A₄.
Its order is six or twelve; order six has a normal subgroup of order three
and hence a nontrivial two-group quotient. Thus its image is all of A₄.
No normality of D in A₆ or in the fixed subgroup is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, proof of
13.6.6, the S₆ paragraph on printed p.927; GLS vol.3, §5.2 for the actual
permutation centralizers. The fixed-group equivalences retain the literal
six-point conjugation action, including the triple-transposition case.
-/

public section

namespace Theory.SpecificGroups.SymmetricSix.CubicCentralizers

open Subgroup Equiv Equiv.Perm AlternatingSix.ShadowLocal GLS3.Chapter5

private theorem card_ne_six_of_twoPerfect {G : Type*} [Group G] [Finite G]
    (hp : IsPPerfect 2 G) : Nat.card G ≠ 6 := by
  intro hc
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hc]; decide)
  let C := zpowers g
  have hC : Nat.card C = 3 := by rw [Nat.card_zpowers, hg]
  have hi : C.index = 2 := by
    have hm := C.card_mul_index
    rw [hC, hc] at hm
    omega
  let hN : C.Normal := normal_of_index_eq_two hi
  have hq : IsPGroup 2 (G ⧸ C) := IsPGroup.of_card (n := 1) hi
  have he := hp C hN hq
  have ht : C.index = 1 := index_eq_one.mpr he
  omega

private theorem fourPoint_recognition (H : Subgroup (Perm (Fin 4)))
    (hp : IsPPerfect 2 H) (h3 : 3 ∣ Nat.card H) (h2 : 2 ∣ Nat.card H) :
    H = alternatingGroup (Fin 4) := by
  have hle : H ≤ alternatingGroup (Fin 4) := by
    rw [← twoResidual_eq_alternating]
    exact le_pResidual_of_isPPerfect H hp
  have hc : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num [Nat.factorial]
  have hd := card_dvd_of_le hle
  rw [hc] at hd
  have hne := card_ne_six_of_twoPerfect hp
  have hcard : Nat.card H = 12 := by
    have hs : 6 ∣ Nat.card H :=
      (show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd h2 h3
    have hpos := Nat.card_pos (α := H)
    have hbound := Nat.le_of_dvd (by decide : 0 < 12) hd
    omega
  exact eq_of_le_of_card_ge hle (by rw [hcard, hc])

/-- A two-perfect subgroup of A₆ with order divisible by six, centralized
pointwise by an actual involution of S₆, is isomorphic to A₄. -/
theorem equiv_alternatingFour (D : Subgroup (Perm (Fin 6)))
    (hDa : D ≤ alternatingGroup (Fin 6)) (hp : IsPPerfect 2 D)
    (h3 : 3 ∣ Nat.card D) (h2 : 2 ∣ Nat.card D)
    (σ : Perm (Fin 6)) (ho : orderOf σ = 2) (hσD : σ ∈ centralizer (D : Set _)) :
    Nonempty (D ≃* alternatingGroup (Fin 4)) := by
  let g : D →* A6 := D.subtype.codRestrict _ (fun x => hDa x.property)
  have hfixed (x : D) : g x ∈ automorphismFixedSubgroup (permutationAction σ) := by
    apply Subtype.ext
    change σ * (x : Perm (Fin 6)) * σ⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact (mem_centralizer_iff.mp hσD x x.property).symm
  let f : D →* automorphismFixedSubgroup (permutationAction σ) :=
    g.codRestrict _ hfixed
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z => z.val.val) h)
  have hodd : σ ∉ alternatingGroup (Fin 6) := by
    intro heven
    let a : A6 := ⟨σ, heven⟩
    have ha : orderOf a = 2 := by
      exact (orderOf_injective (alternatingGroup (Fin 6)).subtype
        (alternatingGroup (Fin 6)).subtype_injective a).symm.trans ho
    have hd := h3.trans (card_dvd_of_injective f hf)
    rw [show permutationAction σ = MulAut.conj a from permutationAction_coe a,
      inner_involution_fixed_card a ha] at hd
    norm_num at hd
  have he : Nonempty (automorphismFixedSubgroup (permutationAction σ) ≃* Perm (Fin 4)) := by
    rcases odd_involution_cycleType σ ho hodd with hs | ht
    · exact ⟨swapFixedEquiv σ hs⟩
    · exact ⟨tripleSwapFixedEquiv σ ht⟩
  obtain ⟨e⟩ := he
  let j : D →* Perm (Fin 4) := e.toMonoidHom.comp f
  have hj : Function.Injective j := e.injective.comp hf
  let eD : D ≃* j.range := MonoidHom.ofInjective hj
  have hperfect : IsPPerfect 2 j.range := hp.of_surjective eD.toMonoidHom eD.surjective
  have hcard : Nat.card D = Nat.card j.range := Nat.card_congr eD.toEquiv
  have hrange := fourPoint_recognition j.range hperfect (hcard ▸ h3) (hcard ▸ h2)
  exact ⟨eD.trans (MulEquiv.subgroupCongr hrange)⟩

end Theory.SpecificGroups.SymmetricSix.CubicCentralizers
