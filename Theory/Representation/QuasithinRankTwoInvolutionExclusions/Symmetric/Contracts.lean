module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The conjugate-product convention

The source writes `vʰ = h⁻¹vh`. This predicate retains that convention and
the literal element order. Equivalences of groups preserve the predicate.
It is an explicit input to the symmetric-module calculations, discharged
from intrinsic type a₂ by `Symmetric.SymplecticBound`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.11.2(4–5), printed p.364 (PDF p.375), and the proof of 6.2.19,
printed p.691 (PDF p.708).
-/

@[expose] public section

namespace Representation.RankTwo.Symmetric

/-- The right-conjugation convention in the source's product bound. -/
def SmallConjugateProducts {G : Type*} [Group G] (v : G) : Prop :=
  ∀ h : G, orderOf (v * (h⁻¹ * v * h)) ≤ 4

theorem SmallConjugateProducts.map {G J : Type*} [Group G] [Group J]
    {v : G} (hv : SmallConjugateProducts v) (e : G ≃* J) :
    SmallConjugateProducts (e v) := by
  intro h
  have he : e (v * ((e.symm h)⁻¹ * v * e.symm h)) = e v * (h⁻¹ * e v * h) := by
    simp only [map_mul, map_inv, e.apply_symm_apply]
  rw [← he, e.orderOf_eq]
  exact hv _

end Representation.RankTwo.Symmetric
