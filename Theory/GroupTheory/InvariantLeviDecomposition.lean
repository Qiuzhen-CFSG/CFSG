module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Fixed factors and relative Levi projections

Disjoint invariant factors of a fixed product are individually fixed. A group
with a relative normal factor and a disjoint complement projects onto that
complement: restrict the quotient map to the complement, prove it bijective,
and invert it. The target is the original complement, and the map fixes it
pointwise.

These group-theoretic steps are used in the descent of the Levi decomposition
in GLS3, Theorem 2.6.5(g), from the algebraic decomposition in Theorem 1.13.3(a).
-/

namespace Subgroup

variable {G : Type*} [Group G]

/-- Uniqueness of a product in disjoint subgroups makes both factors fixed. -/
public theorem fixed_factors_of_disjoint (σ : G →* G) (U L : Subgroup G)
    (hdis : Disjoint U L)
    (hU : ∀ u ∈ U, σ u ∈ U) (hL : ∀ l ∈ L, σ l ∈ L)
    {u l : G} (hu : u ∈ U) (hl : l ∈ L) (hfix : σ (u * l) = u * l) :
    σ u = u ∧ σ l = l := by
  have hpair : (⟨σ u, hU u hu⟩, ⟨σ l, hL l hl⟩) =
      ((⟨u, hu⟩ : U), (⟨l, hl⟩ : L)) :=
    mul_injective_of_disjoint hdis (by simpa only [map_mul] using hfix)
  exact ⟨congrArg (fun x : U × L => x.1.1) hpair,
    congrArg (fun x : U × L => x.2.1) hpair⟩

/-- A relative semidirect decomposition gives a surjective retraction onto the
actual complement, with the relative normal subgroup as its kernel. -/
public theorem exists_projection_of_disjoint_factorization (P U L : Subgroup G)
    (hLP : L ≤ P) (hN : (U.subgroupOf P).Normal)
    (hdis : Disjoint U L)
    (hmul : ∀ x ∈ P, ∃ u ∈ U, ∃ l ∈ L, x = u * l) :
    ∃ f : P →* L, Function.Surjective f ∧ f.ker = U.subgroupOf P ∧
      ∀ l : L, f ⟨l, hLP l.property⟩ = l := by
  let := hN
  let q : P →* P ⧸ U.subgroupOf P := QuotientGroup.mk' _
  let j : L →* P := Subgroup.inclusion hLP
  let r := q.comp j
  have hrinj : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply bot_unique
    intro l hl
    have hlU : (l : G) ∈ U := (QuotientGroup.eq_one_iff (j l)).mp hl
    apply Subtype.ext
    exact (disjoint_iff_inf_le.mp hdis) ⟨hlU, l.property⟩
  have hrsurj : Function.Surjective r := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf P) y
    obtain ⟨u, hu, l, hl, hmul⟩ := hmul x x.property
    refine ⟨⟨l, hl⟩, ?_⟩
    change q (j ⟨l, hl⟩) = q x
    apply (QuotientGroup.eq).mpr
    change ((j ⟨l, hl⟩ : P)⁻¹ * x : P) ∈ U.subgroupOf P
    have hxj : x * (j ⟨l, hl⟩)⁻¹ ∈ U.subgroupOf P := by
      change (x : G) * l⁻¹ ∈ U
      rw [hmul, mul_inv_cancel_right]
      exact hu
    simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] using
      hN.conj_mem (x * (j ⟨l, hl⟩)⁻¹) hxj (j ⟨l, hl⟩)⁻¹
  let e : L ≃* P ⧸ U.subgroupOf P := MulEquiv.ofBijective r ⟨hrinj, hrsurj⟩
  let f := e.symm.toMonoidHom.comp q
  refine ⟨f, e.symm.surjective.comp (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · ext x
    change e.symm (q x) = 1 ↔ x ∈ U.subgroupOf P
    rw [map_eq_one_iff e.symm e.symm.injective]
    exact QuotientGroup.eq_one_iff x
  · intro l
    exact e.symm_apply_apply l

end Subgroup
