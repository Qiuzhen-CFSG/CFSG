module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.ProductTori
public import Theory.SpecificGroups.ReeF4.CentralCovers.PrimaryReduction

/-!
# Odd-prime sections from concrete Ree local geometry

Central transfer and the local lifting calculations reduce every odd prime
to two geometric constructions: the abelian or cyclic Sylow configuration
at primes greater than three, and the torus-plus-cycle configuration at
three. No geometry is requested for primes absent from the actual group
order. The resulting exclusion applies to arbitrary finite perfect covers.

In particular, a cover of odd prime degree cannot exist, so it satisfies
the precise Sylow-section implication consumed by `PrimaryReduction`.
The geometric configurations remain explicit hypotheses: this is not yet
the unconditional Ree multiplier theorem. Their constructors must establish
existence for `m ≥ 1` on the literal `Model m`, independently of any cover.

Source: Aschbacher–Smith I.1.1–4, printed pp.407–408 of
`refs/quasithin.pdf`, and GLS3 §6.1. The full binary group `Model 0` and
the Tits simple group remain distinct.
-/

public section

namespace ReeF4.CentralCovers.OddPrimary

open PerfectCentralCovering

universe u

/-- The remaining geometric inputs exclude every odd prime from every
finite perfect central kernel on this literal model. -/
theorem not_dvd_kernel_of_geometry (m : ℕ)
    (hgood : ∀ (p : ℕ) (_hp : p.Prime), 3 < p → p ∣ Nat.card (Model m) →
      GoodPrimeGeometry m p)
    (hthree : Nonempty (ThreeSylowData m))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {E : Type u} [Group E] [Finite E] (c : Cover E (Model m)) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  by_cases hp3 : p = 3
  · subst p
    obtain ⟨D⟩ := hthree
    exact D.not_three_dvd_kernel c
  by_cases hd : p ∣ Nat.card (Model m)
  · have hlarge : 3 < p := by have := (Fact.out : p.Prime).two_le; omega
    exact (hgood p Fact.out hlarge hd).not_dvd_kernel hp c
  · exact (goodPrimeGeometry_of_not_dvd_card hd).not_dvd_kernel hp c

/-- The exact prime-degree section contract used by the parent. Its
geometric premises must still be constructed before removing `of_geometry`. -/
theorem prime_sylow_section_of_geometry (m : ℕ)
    (hgood : ∀ (p : ℕ) (_hp : p.Prime), 3 < p → p ∣ Nat.card (Model m) →
      GoodPrimeGeometry m p)
    (hthree : Nonempty (ThreeSylowData m))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {F : Type u} [Group F] [Finite F] (d : Cover F (Model m))
    (hd : Nat.card d.toMonoidHom.ker = p) :
    ∃ (P : Sylow p (Model m)) (s : P →* F),
      d.toMonoidHom.comp s = (P : Subgroup (Model m)).subtype := by
  exact False.elim ((not_dvd_kernel_of_geometry m hgood hthree hp d)
    (hd.symm ▸ dvd_refl p))

/-- Application of the new section implication to the published prime-kernel
reduction, using its literal Sylow subtype map. -/
theorem not_dvd_kernel_via_primaryReduction (m : ℕ)
    (hgood : ∀ (p : ℕ) (_hp : p.Prime), 3 < p → p ∣ Nat.card (Model m) →
      GoodPrimeGeometry m p)
    (hthree : Nonempty (ThreeSylowData m))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {E : Type u} [Group E] [Finite E] (c : Cover E (Model m)) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  apply not_dvd_kernel_of_prime_sylow_sections m _ c
  intro F _ _ d hd
  exact prime_sylow_section_of_geometry m hgood hthree hp d hd

end ReeF4.CentralCovers.OddPrimary
