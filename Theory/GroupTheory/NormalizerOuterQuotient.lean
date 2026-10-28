module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.PGroup

/-!
# Outer automorphisms realized in an overgroup

For a subgroup H of G, conjugation induces a homomorphism from N_G(H)/H
to Aut(H)/Inn(H). It is surjective when the normalizer realizes every
automorphism of H. Thus a p-power relative index of H in its normalizer
makes the actual outer automorphism group a p-group.

The normal subgroup used in the quotient is H inside N_G(H); no normality
in G is required. This is the elementary quotient step in permutation
realizations of the outer groups tabulated in GLS3, Section 5.3.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- Conjugation on H, modulo its inner automorphisms. -/
@[expose] def normalizerOuterHom (H : Subgroup G) :
    (normalizer (H : Set G) ⧸ H.subgroupOf (normalizer (H : Set G))) →*
      MulAut.Outer H :=
  QuotientGroup.map _ _ H.normalizerMonoidHom (by
    intro n hn
    exact ⟨⟨n, hn⟩, by ext x; rfl⟩)

/-- Coverage of all automorphisms gives coverage of the outer quotient. -/
theorem normalizerOuterHom_surjective (H : Subgroup G)
    (h : Function.Surjective H.normalizerMonoidHom) :
    Function.Surjective (normalizerOuterHom H) := by
  intro q
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup H) q
  obtain ⟨n, rfl⟩ := h α
  exact ⟨QuotientGroup.mk' _ n, rfl⟩

/-- A p-power normalizer index controls Out(H) once conjugation covers Aut(H). -/
theorem outer_isPGroup_of_normalizer_relIndex (H : Subgroup G) {p n : ℕ}
    (h : Function.Surjective H.normalizerMonoidHom)
    (hi : H.relIndex (normalizer (H : Set G)) ∣ p ^ n) :
    IsPGroup p (MulAut.Outer H) := by
  have hN : IsPGroup p
      (normalizer (H : Set G) ⧸ H.subgroupOf (normalizer (H : Set G))) := by
    apply IsPGroup.of_card_dvd_pow (n := n)
    rwa [← index_eq_card]
  exact hN.of_surjective (normalizerOuterHom H) (normalizerOuterHom_surjective H h)

end Subgroup
