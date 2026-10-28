module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.PGroup

/-!
# Outer automorphisms realized by a normalizer

For a subgroup H of G, conjugation induces a homomorphism
N_G(H)/H → Out(H). If the normalizer realizes every automorphism of H,
this homomorphism is surjective. Consequently a p-group calculation for
the normalizer quotient controls the full outer automorphism group.

The denominator is the copy of H inside its normalizer; H need not be
normal in G. No assertion that a constructed subgroup realizes every
automorphism is implicit in this reduction.

This is the normalizer realization route to the outer-group calculation
in GLS3, Table 5.3p, used for Held's group in Aschbacher–Smith, printed p.510.
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- Conjugation by the normalizer, modulo the inner automorphisms of H. -/
public def normalizerOuterAction (H : Subgroup G) :
    normalizer (H : Set G) ⧸ H.subgroupOf (normalizer (H : Set G)) →*
      MulAut.Outer H :=
  QuotientGroup.map _ _ H.normalizerMonoidHom (by
    intro x hx
    refine ⟨⟨x.val, hx⟩, ?_⟩
    ext y
    rfl)

/-- The induced quotient map sends a coset to the class of its conjugation. -/
public theorem normalizerOuterAction_mk (H : Subgroup G)
    (g : normalizer (H : Set G)) :
    normalizerOuterAction H (QuotientGroup.mk g) =
      QuotientGroup.mk (H.normalizerMonoidHom g) := by
  exact QuotientGroup.map_mk _ _ _ _ g

/-- Realization of every automorphism makes the map onto the full outer group
surjective. This is an explicit hypothesis, separate from a normalizer computation. -/
public theorem normalizerOuterAction_surjective (H : Subgroup G)
    (h : Function.Surjective H.normalizerMonoidHom) :
    Function.Surjective (normalizerOuterAction H) := by
  intro x
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup H) x
  obtain ⟨g, rfl⟩ := h f
  exact ⟨QuotientGroup.mk' (H.subgroupOf (normalizer (H : Set G))) g, rfl⟩

/-- A p-group normalizer quotient controls Out(H) when all automorphisms
are realized by the normalizer. -/
public theorem isPGroup_outer_of_normalizer (H : Subgroup G) (p : ℕ)
    (h : Function.Surjective H.normalizerMonoidHom)
    (hp : IsPGroup p
      (normalizer (H : Set G) ⧸ H.subgroupOf (normalizer (H : Set G)))) :
    IsPGroup p (MulAut.Outer H) :=
  hp.of_surjective (normalizerOuterAction H) (normalizerOuterAction_surjective H h)

end Subgroup
