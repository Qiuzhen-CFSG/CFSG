module

public import Theory.SpecificGroups.AlternatingSix.SylowFixedAction
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.NaturalFixed
public import Theory.GroupAction.SylowFixedInvolution
public import Theory.GroupTheory.PPrimeCorePGroupQuotient
public import Theory.SpecificGroups.SymmetricFourOddCore

/-!
# Odd cores of Sylow-fixing A₆ automorphism centralizers

Let H act faithfully on the actual A₆ and contain all its inner automorphisms.
For an actor a, the inner part of C_H(a) is isomorphic to the fixed subgroup
of its automorphism on A₆. The quotient above that inner part has order
dividing four, since Inn(A₆) is normal of index four in Aut(A₆). Thus triviality
of the odd core of the fixed subgroup implies the same for C_H(a).

An involution fixing a Sylow two-subgroup belongs to the natural S₆. Its fixed
subgroup has order eight in the inner case and is actually isomorphic to S₄
in the outer case. Both have trivial odd core. An order-two actor subgroup is
cyclic, so its centralizer is the centralizer of its nonidentity element.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.19,
printed p.252 (PDF p.263). The A₆ fixed-group calculations are the intrinsic
GLS, Volume 3, §5.2 results exposed by the imported geometry leaves.
-/

public section

open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal
variable {H : Type*} [Group H]

private theorem inner_centralizer_equiv_fixed (φ : H →* AutA6)
    (hφ : Function.Injective φ) (hinner : inner ≤ φ.range) (a : H) :
    Nonempty ((inner.comap (φ.comp (centralizer ({a} : Set H)).subtype)) ≃*
      automorphismFixedSubgroup (φ a)) := by
  let C := centralizer ({a} : Set H)
  let N := inner.comap (φ.comp C.subtype)
  let f : N →* A6 := innerEquiv.symm.toMonoidHom.comp
    ((φ.comp (C.subtype.comp N.subtype)).codRestrict inner (fun x => x.property))
  have hf (x : N) : MulAut.conj (f x) = φ x.val.val := by
    exact congrArg Subtype.val (innerEquiv.apply_symm_apply
      ⟨φ x.val.val, x.property⟩)
  have hfix (x : N) : φ a (f x) = f x := by
    apply inner_injective
    rw [← aut_conj_inner, hf]
    have hx := congrArg φ (mem_centralizer_singleton_iff.mp x.val.property)
    simp only [map_mul] at hx
    rw [← hx, mul_inv_cancel_right]
  let j : N →* automorphismFixedSubgroup (φ a) := f.codRestrict _ hfix
  refine ⟨MulEquiv.ofBijective j ⟨?_, ?_⟩⟩
  · intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply hφ
    rw [← hf x, ← hf y]
    exact congrArg MulAut.conj (congrArg Subtype.val hxy)
  · intro x
    obtain ⟨h, hh⟩ := hinner (show MulAut.conj x.val ∈ inner from ⟨x.val, rfl⟩)
    have hc : h ∈ C := by
      apply mem_centralizer_singleton_iff.mpr
      apply hφ
      simp only [map_mul, hh]
      have he := aut_conj_inner (φ a) x.val
      rw [show φ a x.val = x.val from x.property] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    let n : N := ⟨⟨h, hc⟩, by change φ h ∈ inner; rw [hh]; exact ⟨x.val, rfl⟩⟩
    refine ⟨n, Subtype.ext ?_⟩
    apply inner_injective
    exact (hf n).trans hh

private theorem centralizer_oddCore_eq_bot_of_fixed [Finite H]
    (φ : H →* AutA6) (hφ : Function.Injective φ) (hinner : inner ≤ φ.range) (a : H)
    (hfixed : pPrimeCore 2 (automorphismFixedSubgroup (φ a)) = ⊥) :
    pPrimeCore 2 (centralizer ({a} : Set H)) = ⊥ := by
  let C := centralizer ({a} : Set H)
  let N := inner.comap (φ.comp C.subtype)
  obtain ⟨e⟩ := inner_centralizer_equiv_fixed φ hφ hinner a
  have hN : pPrimeCore 2 N = ⊥ :=
    (map_eq_bot_iff_of_injective _ e.injective).mp
      ((pPrimeCore_map_iso 2 e).trans hfixed)
  have hQ : IsPGroup 2 (C ⧸ N) := by
    apply IsPGroup.of_card_dvd_pow (n := 2)
    change N.index ∣ 2 ^ 2
    rw [show N = inner.comap (φ.comp C.subtype) from rfl, index_comap]
    simpa only [inner_index, Nat.reducePow] using inner.relIndex_dvd_index_of_normal (φ.comp C.subtype).range
  exact pPrimeCore_eq_bot_of_isPGroup_quotient 2 N hN hQ

/-- A faithful inner-containing action on A₆ with a Sylow-fixing involution
subgroup has trivial odd core in its centralizer. -/
theorem sylowFixedInvolution_centralizer_oddCore_eq_bot [Finite H]
    (φ : H →* AutA6) (E : Subgroup H)
    (d : Theory.GroupAction.SylowFixedInvolution φ E) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := E) 2 (by rw [d.card])
  have haH : orderOf (a : H) = 2 := (orderOf_injective E.subtype E.subtype_injective a).trans ha
  have he : zpowers (a : H) = E := eq_of_le_of_card_ge
    (zpowers_le.mpr a.property) (by rw [Nat.card_zpowers, haH, d.card])
  have hC : centralizer (E : Set H) = centralizer ({(a : H)} : Set H) := by
    calc
      _ = centralizer (zpowers (a : H) : Set H) :=
        congrArg (fun K : Subgroup H => centralizer (K : Set H)) he.symm
      _ = _ := by rw [zpowers_eq_closure, centralizer_closure]
  rw [hC]
  apply centralizer_oddCore_eq_bot_of_fixed φ d.faithful d.inner a
  have hβ : orderOf (φ a) = 2 := (orderOf_injective φ d.faithful a).trans haH
  obtain ⟨P, hP⟩ := d.fixes
  have hn : φ a ∈ natural := involution_mem_natural_of_fixes_sylow P (φ a) hβ
    (hP a a.property)
  by_cases hi : φ a ∈ inner
  · obtain ⟨x, hx⟩ := hi
    have ho : orderOf x = 2 := (orderOf_injective (MulAut.conj : A6 →* AutA6)
      inner_injective x).symm.trans (hx ▸ hβ)
    rw [← hx]
    apply card_eq_one.mp
    have hd := (pPrimeCore 2 (automorphismFixedSubgroup (MulAut.conj x))).card_subgroup_dvd_card
    rw [inner_involution_fixed_card x ho] at hd
    exact Nat.eq_one_of_dvd_coprimes
      ((pPrimeCore_coprime_card (p := 2) (G := automorphismFixedSubgroup (MulAut.conj x))).pow_left 3)
      hd dvd_rfl
  · obtain ⟨e⟩ := natural_outer_involution_fixed_equiv_symmetricFour (φ a) hβ hn hi
    exact (map_eq_bot_iff_of_injective _ e.injective).mp
      ((pPrimeCore_map_iso 2 e).trans SymmetricFour.oddCore_eq_bot)

end AlternatingSix.ShadowLocal
