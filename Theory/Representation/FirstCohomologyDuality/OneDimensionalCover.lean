module

public import Theory.Representation.FirstCohomologyDuality

/-!
# Comparing covers with one-dimensional dual first cohomology

If the dual of a finite-dimensional module has first cohomology of dimension
one, every perfect central cover with nonzero kernel is isomorphic to any
perfect central cover whose dimension is one larger than the base. Both are
quotients of the explicit universal cover. Rank-nullity makes their quotient
maps bijective and hence gives an equivariant linear identification.

Reference: Aschbacher–Smith, Remark I.1.5, printed p.408 (PDF p.419).
-/

@[expose] public section

open Module Representation
namespace Representation.OneCohomology
variable {k G N V W : Type*} [Field k] [Group G]
  [AddCommGroup N] [Module k N] [FiniteDimensional k N]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  {ρ : Representation k G N} {σ : Representation k G V} {τ : Representation k G W}

/-- A nontrivial cover is identified with a cover of maximal dimension. -/
lemma equiv_of_cover_of_finrank_dual_H1_eq_one [Finite G]
    (p : σ.IntertwiningMap ρ) (hp : IsCover p)
    (q : τ.IntertwiningMap ρ) (hq : IsCover q)
    (hH : finrank k (H1 ρ.dual) = 1)
    (hV : p.toLinearMap.ker ≠ ⊥)
    (hW : finrank k W = finrank k N + 1) :
    ∃ f : V ≃ₗ[k] W, ∀ g v, f (σ g v) = τ g (f v) := by
  have : FiniteDimensional k (Module.Dual k (cocycles ρ.dual)) :=
    Subspace.instModuleDualFiniteDimensional (K := k) (V := cocycles ρ.dual)
  obtain ⟨a, ha, hap⟩ := exists_universalCover_quotient p hp
  obtain ⟨b, hb, hbq⟩ := exists_universalCover_quotient q hq
  let u := universalCoverProjection ρ
  have hu : Function.Surjective u := by
    intro n
    obtain ⟨v, rfl⟩ := hp.1 n
    obtain ⟨x, rfl⟩ := ha v
    exact ⟨x, (hap x).symm⟩
  have hU := u.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hu, finrank_top,
    finrank_ker_universalCoverProjection, hH] at hU
  have hVp := p.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp.1, finrank_top] at hVp
  have hpos : 0 < finrank k p.toLinearMap.ker := by
    have : finrank k p.toLinearMap.ker ≠ 0 := fun h =>
      hV (Submodule.finrank_eq_zero.mp h)
    omega
  have hle := LinearMap.finrank_le_finrank_of_surjective (f := a.toLinearMap) ha
  have hVU : finrank k V = finrank k (Module.Dual k (cocycles ρ.dual)) := by omega
  have hWU : finrank k W = finrank k (Module.Dual k (cocycles ρ.dual)) := by omega
  let A := LinearEquiv.ofBijective a.toLinearMap
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hVU.symm).mpr ha, ha⟩
  let B := LinearEquiv.ofBijective b.toLinearMap
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hWU.symm).mpr hb, hb⟩
  refine ⟨A.symm.trans B, ?_⟩
  intro g v
  have he : A.symm (σ g v) = (universalAction ρ.dual).dual g (A.symm v) := by
    apply A.injective
    change A (A.symm (σ g v)) = a ((universalAction ρ.dual).dual g (A.symm v))
    rw [A.apply_symm_apply, a.isIntertwining]
    exact congrArg (σ g) (A.apply_symm_apply v).symm
  change B (A.symm (σ g v)) = τ g (B (A.symm v))
  rw [he]
  change b ((universalAction ρ.dual).dual g (A.symm v)) = τ g (b (A.symm v))
  exact LinearMap.congr_fun (b.isIntertwining' g) (A.symm v)
end Representation.OneCohomology
