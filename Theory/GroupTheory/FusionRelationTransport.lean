module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.Group

/-!
# Transport of normalizer fusion relations

Let `R` be a transitive relation on a subgroup `P` that contains conjugacy
inside `P`. If normalizer steps at a subgroup `V` preserve `R`, the same is
true at every conjugate of `V` by an element of `P`. The subgroups and their
normalizers live in the ambient group, while the elements related by `R`
live in the actual subgroup type `P`. No finiteness, Sylow, or extremality
hypothesis is needed for this transport.

If `U = s V s⁻¹` and `g ∈ N_G(U)` takes `x` to `y` by right conjugation,
conjugate the entire step by `s⁻¹`. The resulting normalizer element
`s⁻¹ g s` acts at `V` between `s⁻¹ x s` and `s⁻¹ y s`. Apply the local
hypothesis and compose with conjugacies inside `P` at both endpoints.

This is the representative-transport step used in ABG Chapter II §1,
Proposition 1 (article pp.10–11), following the conjugacy representatives
of Lemma 1(ii). It is stated here as general subgroup mathematics.
-/

namespace Subgroup

/-- A transitive relation containing subgroup conjugacy inherits normalizer
fusion preservation from any conjugate representative inside that subgroup. -/
public theorem normalizer_fusion_relation_of_conjugate
    {G : Type*} [Group G] (P U V : Subgroup G) (R : P → P → Prop)
    (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hconjR : ∀ {x y : P}, IsConj x y → R x y)
    (s : P) (hconj : V.map (MulAut.conj (s : G)).toMonoidHom = U)
    (hlocal : ∀ g : G, g ∈ normalizer (V : Set G) →
      ∀ x y : P, (x : G) ∈ V → g⁻¹ * (x : G) * g = (y : G) → R x y)
    (g : G) (hg : g ∈ normalizer (U : Set G))
    (x y : P) (hxU : (x : G) ∈ U)
    (hxy : g⁻¹ * (x : G) * g = (y : G)) : R x y := by
  let x' : P := s⁻¹ * x * s
  let y' : P := s⁻¹ * y * s
  let g' : G := (s : G)⁻¹ * g * (s : G)
  have hxV : (x' : G) ∈ V := by
    rw [← hconj, mem_map_equiv] at hxU
    exact hxU
  have hgV : g' ∈ normalizer (V : Set G) := by
    have hnorm := map_equiv_normalizer_eq V (MulAut.conj (s : G))
    rw [hconj] at hnorm
    rw [← hnorm, mem_map_equiv] at hg
    exact hg
  have hxy' : g'⁻¹ * (x' : G) * g' = (y' : G) := by
    change ((s : G)⁻¹ * g * (s : G))⁻¹ *
      ((s : G)⁻¹ * (x : G) * (s : G)) * ((s : G)⁻¹ * g * (s : G)) =
      (s : G)⁻¹ * (y : G) * (s : G)
    calc
      _ = (s : G)⁻¹ * (g⁻¹ * (x : G) * g) * (s : G) := by group
      _ = _ := by rw [hxy]
  have hxx' : IsConj x x' := by
    apply isConj_iff.mpr
    refine ⟨s⁻¹, ?_⟩
    simp [x']
  have hy'y : IsConj y' y := by
    apply isConj_iff.mpr
    refine ⟨s, ?_⟩
    simp [y', mul_assoc]
  exact htrans (hconjR hxx') (htrans (hlocal g' hgV x' y' hxV hxy') (hconjR hy'y))

end Subgroup
