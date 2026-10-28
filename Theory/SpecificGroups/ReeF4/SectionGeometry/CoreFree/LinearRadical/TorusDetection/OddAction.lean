module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.Levi
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.PositiveTwoGroup
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.Frattini.PGroup

/-!
# Odd torus action on the linear Ree radical

An odd-order normalizing element acting trivially on a finite two-group's
abelianization centralizes the group. Its induced automorphism lies in the
Burnside Frattini kernel, a two-group, and has odd order, hence is trivial.
The commutator hypothesis is transported from the ambient group to the
radical's own derived subgroup before passing to the Frattini quotient.

For the full fixed Ree torus, oddness follows from its inclusion in the
split diagonal torus. The specified radical is a two-group because its
root support lies in the positive subgroup. Relative normality supplies
the conjugation action without a simplicity assumption.

Source: the torus part of GLS3, Theorem 2.6.5(e),
`refs/KGroup/GLS3/chapter2.tex`; Burnside's Frattini automorphism kernel.
-/

open Subgroup
open scoped commutatorElement
noncomputable section

namespace ReeF4.SectionGeometry.LinearRadical
open LargeLocalSeeds Parabolics

private theorem centralizes_of_odd_order
    {G : Type*} [Group G] [Finite G] (R : Subgroup G) (hR : IsPGroup 2 R)
    (g : normalizer (R : Set G)) (hg : Odd (orderOf g))
    (hcomm : ∀ q ∈ R, ⁅(g : G), q⁆ ∈ ⁅R, R⁆) :
    ∀ q ∈ R, (g : G) * q * (g : G)⁻¹ = q := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 R) := ⟨hR⟩
  let a := R.normalizerMonoidHom g
  have hker : a ∈ (quotientAut (frattini R)).ker := by
    apply MulEquiv.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini R) q
    rw [quotientAut_apply_mk]
    change (QuotientGroup.mk' (frattini R)) (a x) = (QuotientGroup.mk' (frattini R)) x
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply commutator_le_frattini_of_isPGroup (p := 2)
    have hh : ((a x / x : R) : G) ∈ ⁅R, R⁆ := by
      simpa only [a, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.normalizerMonoidHom_apply_apply_coe, commutatorElement_def] using hcomm x x.property
    rw [← map_subtype_commutator R] at hh
    obtain ⟨y, hy, he⟩ := hh
    have hxy : y = a x / x := Subtype.ext he
    exact hxy ▸ hy
  let b : (quotientAut (frattini R)).ker := ⟨a, hker⟩
  obtain ⟨n, hn⟩ := (isPGroup_quotientAut_frattini_kernel hR).exists_orderOf_dvd_pow b
  have hdiv : orderOf b ∣ orderOf g := by
    rw [← orderOf_injective _ (quotientAut (frattini R)).ker.subtype_injective b]
    exact orderOf_map_dvd R.normalizerMonoidHom g
  have hbone : b = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hg.coprime_two_right.pow_right n) hdiv hn)
  have ha : a = 1 := congrArg Subtype.val hbone
  intro q hq
  exact congrArg (fun f : MulAut R => (f ⟨q, hq⟩ : G)) ha

/-- Trivial action of a full fixed-torus element on the radical abelianization
forces pointwise centralization of the specified linear radical. -/
public theorem fixedTorus_centralizes_radical_of_trivial_abelianization
    (m : ℕ) (t : Model m) (ht : t ∈ fixedTorus m)
    (ha : ActsTriviallyOnRadicalAbelianization m t) :
    ∀ q ∈ radical m .linear, t * q * t⁻¹ = q := by
  have hR : IsPGroup 2 (radical m .linear) :=
    ((splitUnipotent_isPGroup m).to_le (splitRadical_le_unipotent m .linear)).comap_of_injective
      (toSplitGroup m) (toSplitGroup_injective m)
  have hn : t ∈ normalizer (radical m .linear : Set (Model m)) :=
    parabolic_le_radical_normalizer m .linear
      (fullLevi_le_parabolic m (fixedTorus_le_fullLevi m ht))
  have hodd : Odd (orderOf (⟨t, hn⟩ : normalizer (radical m .linear : Set (Model m)))) := by
    rw [← orderOf_injective _ (normalizer (radical m .linear : Set (Model m))).subtype_injective]
    change Odd (orderOf t)
    have hT : Odd (Nat.card (splitTorus m)) := by
      rw [splitTorus_eq_diagonalTorus]
      exact diagonalTorus_odd_card m
    rw [← orderOf_injective _ (toSplitGroup_injective m)]
    exact hT.of_dvd_nat ((splitTorus m).orderOf_dvd_natCard ht)
  exact centralizes_of_odd_order (radical m .linear) hR ⟨t, hn⟩ hodd ha

end ReeF4.SectionGeometry.LinearRadical
