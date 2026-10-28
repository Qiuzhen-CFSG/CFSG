module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Involution orbit cancellation

In characteristic two, a sum invariant under conjugation by an element of
square one equals its sum over that element's centralizer. Conjugation is an
involution, and every nonfixed orbit is a pair of equal terms, which cancel.
This is the combinatorial input to Brauer restriction multiplicativity and
augmentation preservation. No nonidentity assumption on the element is
needed.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BrauerMapScratch.lean` (revision `c3503435`), the
orbit-cancellation step in the special case of Feit III.7.1 used for Z*.
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock.BrauerMap

universe u v

attribute [local instance] Fintype.ofFinite

private theorem conjugateBy_involution_involutive
    {G : Type v} [Group G] {z : G} (hz : z * z = 1) (g : G) :
    z * (z * g * z⁻¹) * z⁻¹ = g := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  rw [hzinv]
  calc
    z * (z * g * z) * z = (z * z) * g * (z * z) := by
      simp only [mul_assoc]
    _ = g := by rw [hz]; simp

private theorem conjugateBy_eq_self_of_mem_centralizer
    {G : Type v} [Group G] {z g : G} (hz : z * z = 1)
    (hg : g ∈ Subgroup.centralizer ({z} : Set G)) :
    z * g * z⁻¹ = g := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hcomm : g * z = z * g :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  rw [hzinv, ← hcomm]
  simp only [mul_assoc]
  rw [hz, mul_one]

private theorem mem_centralizer_of_conjugateBy_eq_self
    {G : Type v} [Group G] {z g : G} (hz : z * z = 1)
    (hg : z * g * z⁻¹ = g) :
    g ∈ Subgroup.centralizer ({z} : Set G) := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have h := congrArg (fun x : G => x * z) hg
  have hzg : z * g = g * z := by
    simpa only [hzinv, mul_assoc, hz, mul_one] using h
  exact hzg.symm

/-- Orbit cancellation under conjugation by an involution.  Centrality makes
the summand constant on each conjugation orbit, and every orbit outside the
centralizer has size two, hence contributes zero in characteristic two. -/
private theorem sum_eq_sum_centralizer_of_conj_invariant
    {R : Type u} {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G] [DecidableEq G]
    (z : G)
    [DecidablePred (fun g : G =>
      g ∈ Subgroup.centralizer ({z} : Set G))]
    (hz : z * z = 1) (F : G → R)
    (hF : ∀ g : G, F (z * g * z⁻¹) = F g) :
    ∑ g : G, F g =
      ∑ g ∈ (Finset.univ : Finset G) with
        g ∈ Subgroup.centralizer ({z} : Set G), F g := by
  classical
  let moved : Finset G := Finset.univ.filter
    (fun g => g ∉ Subgroup.centralizer ({z} : Set G))
  have hmoved : ∑ g ∈ moved, F g = 0 := by
    refine Finset.sum_involution
      (s := moved) (f := F)
      (g := fun g _hg => z * g * z⁻¹) ?_ ?_ ?_ ?_
    · intro g _hg
      rw [hF]
      exact CharTwo.add_self_eq_zero _
    · intro g hg _hFg hfixed
      apply (Finset.mem_filter.mp hg).2
      exact mem_centralizer_of_conjugateBy_eq_self hz hfixed
    · intro g hg
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hconjMem
      have hfixed := conjugateBy_eq_self_of_mem_centralizer hz hconjMem
      have hinv := conjugateBy_involution_involutive hz g
      apply (Finset.mem_filter.mp hg).2
      rw [← hinv, hfixed]
      exact hconjMem
    · intro g _hg
      exact conjugateBy_involution_involutive hz g
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset G)
      (fun g => g ∈ Subgroup.centralizer ({z} : Set G)) F
  calc
    ∑ g : G, F g =
        (∑ g ∈ (Finset.univ : Finset G) with
            g ∈ Subgroup.centralizer ({z} : Set G), F g) +
          ∑ g ∈ (Finset.univ : Finset G) with
            g ∉ Subgroup.centralizer ({z} : Set G), F g := hsplit.symm
    _ = ∑ g ∈ (Finset.univ : Finset G) with
          g ∈ Subgroup.centralizer ({z} : Set G), F g := by
      change _ + (∑ g ∈ moved, F g) = _
      rw [hmoved, add_zero]

/-- Public subtype-sum form of involution-orbit cancellation. -/
theorem sum_centralizer_of_conj_invariant
    {R : Type u} {G : Type v}
    [CommRing R] [CharP R 2] [Group G] [Finite G]
    (z : G) (hz : z * z = 1) (F : G → R)
    (hF : ∀ g : G, F (z * g * z⁻¹) = F g) :
    ∑ g : G, F g =
      ∑ h : Subgroup.centralizer ({z} : Set G), F (h : G) := by
  classical
  let : Fintype (Subgroup.centralizer ({z} : Set G)) :=
    Fintype.ofFinite _
  calc
    ∑ g : G, F g =
        ∑ g ∈ (Finset.univ : Finset G) with
          g ∈ Subgroup.centralizer ({z} : Set G), F g :=
      sum_eq_sum_centralizer_of_conj_invariant z hz F hF
    _ = ∑ h : Subgroup.centralizer ({z} : Set G), F (h : G) := by
      rw [← Finset.sum_subtype_eq_sum_filter]
      apply Finset.sum_congr
      · ext h
        simp
      · intro h _hh
        rfl

end ModularBlock.BrauerMap

