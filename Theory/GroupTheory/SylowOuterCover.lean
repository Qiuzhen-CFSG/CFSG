module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow coverage of outer action

If the outer automorphism group of a normal subgroup `N` is a p-group,
then `N`, its centralizer, and any Sylow p-subgroup generate the ambient
finite group. Indeed, the kernel of outer action is `N C_G(N)`, and the
Sylow subgroup maps onto its p-group image. A subgroup containing these
three groups is therefore the whole group.

For Aschbacher--Smith D.3.9(1), printed p.200, apply the containment form
to the inertia subgroup of the local constituent's isomorphism type.
This keeps the centralizer and does not assume it is trivial.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- A Sylow subgroup covers all outer action when the outer group is a p-group. -/
theorem sup_centralizer_sup_sylow_eq_top
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (houter : IsPGroup p (MulAut.Outer N))
    (T : Sylow p G) :
    (N ⊔ centralizer (N : Set G)) ⊔ (T : Subgroup G) = ⊤ := by
  let f : G →* MulAut.Outer N :=
    (QuotientGroup.mk' (MulAut.innerSubgroup N)).comp MulAut.conjNormal
  have hker : f.ker = N ⊔ centralizer (N : Set G) := by
    rw [show f.ker = ((QuotientGroup.mk' (MulAut.innerSubgroup N)).ker).comap
      MulAut.conjNormal from (MonoidHom.comap_ker _ _).symm, QuotientGroup.ker_mk']
    exact MulAut.conjNormal_comap_innerSubgroup N
  let U := T.mapSurjective f.rangeRestrict_surjective
  have htop : (U : Subgroup f.range) = ⊤ :=
    (U.is_maximal' ((houter.to_subgroup f.range).to_subgroup ⊤) le_top).symm
  have hmap : ((T : Subgroup G).map f.rangeRestrict) = ⊤ := htop
  have he := congrArg (Subgroup.comap f.rangeRestrict) hmap
  rw [Subgroup.comap_map_eq, MonoidHom.ker_rangeRestrict, hker,
    Subgroup.comap_top] at he
  simpa only [sup_comm] using he

/-- An inertia subgroup containing inner action, centralizing action, and
a Sylow subgroup contains every ambient element. -/
theorem eq_top_of_inner_centralizer_sylow_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (houter : IsPGroup p (MulAut.Outer N))
    (T : Sylow p G) (I : Subgroup G)
    (hN : N ≤ I) (hC : centralizer (N : Set G) ≤ I)
    (hT : (T : Subgroup G) ≤ I) : I = ⊤ := by
  apply top_unique
  rw [← sup_centralizer_sup_sylow_eq_top N houter T]
  exact sup_le (sup_le hN hC) hT

end Theory.GroupTheory
