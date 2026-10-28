module

public import Theory.Representation.FirstCohomologyDuality

/-!
# Indecomposable central extensions and first cohomology

A surjection from an indecomposable representation onto a nonzero
commutator-generated module is a cover whenever its kernel is fixed.
Indeed the commutator space supplements the kernel. A linear complement to
the commutator space can be chosen inside that fixed kernel, so it is an
invariant direct summand and must vanish.

The universal cover then bounds the central kernel by the first cohomology
of the contragredient quotient. This argument is independent of characteristic
and does not assume the extension splits.

Reference: the covering construction in Aschbacher–Smith, Remark I.1.5,
printed p.408, and its use in the module step of J.2.5, printed p.434
(PDF pp.419, 445 of `refs/quasithin.pdf`).
-/

public section

open Module Representation Representation.OneCohomology
namespace Representation.OneCohomology
variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

private lemma map_commutator_of_surjective (p : σ.IntertwiningMap ρ)
    (hp : Function.Surjective p) :
    (Coinvariants.ker σ).map p.toLinearMap = Coinvariants.ker ρ := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, w⟩, rfl⟩
    change p (σ g w - w) ∈ Coinvariants.ker ρ
    rw [map_sub, p.isIntertwining]
    exact Coinvariants.sub_mem_ker g (p w)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    obtain ⟨w, rfl⟩ := hp v
    exact ⟨σ g w - w, Coinvariants.sub_mem_ker g w, by
      change p (σ g w - w) = _
      rw [map_sub, p.isIntertwining]⟩

/-- An indecomposable central extension of a nonzero perfect module is a cover. -/
lemma isCover_of_indecomposable [Nontrivial V]
    (p : σ.IntertwiningMap ρ) (hp : Function.Surjective p)
    (hfixed : p.toLinearMap.ker ≤ fixed σ)
    (hgen : Coinvariants.ker ρ = ⊤)
    (hind : ∀ A B : Submodule k W,
      (∀ g v, v ∈ A → σ g v ∈ A) →
      (∀ g v, v ∈ B → σ g v ∈ B) → IsCompl A B → A = ⊥ ∨ B = ⊥) :
    IsCover p := by
  refine ⟨hp, hfixed, ?_⟩
  have hm : (Coinvariants.ker σ).map p.toLinearMap = ⊤ :=
    (map_commutator_of_surjective p hp).trans hgen
  have hs : Coinvariants.ker σ ⊔ p.toLinearMap.ker = ⊤ := by
    have h := congrArg (Submodule.comap p.toLinearMap) hm
    simpa only [Submodule.comap_map_eq, Submodule.comap_top] using h
  obtain ⟨C, hC, hcompl⟩ :=
    (show Codisjoint p.toLinearMap.ker (Coinvariants.ker σ) from
      codisjoint_iff.mpr (by simpa only [sup_comm] using hs)).exists_isCompl
  have hCi : ∀ g v, v ∈ C → σ g v ∈ C := by
    intro g v hv
    rw [hfixed (hC hv) g]
    exact hv
  have hMi : ∀ g v, v ∈ Coinvariants.ker σ → σ g v ∈ Coinvariants.ker σ := by
    intro g v hv
    simpa only [sub_add_cancel] using
      (Coinvariants.ker σ).add_mem (Coinvariants.sub_mem_ker g v) hv
  rcases hind C (Coinvariants.ker σ) hCi hMi hcompl with hc | hmzero
  · simpa only [hc, bot_sup_eq] using hcompl.sup_eq_top
  · rw [hmzero, Submodule.map_bot] at hm
    exact False.elim (bot_ne_top hm)

/-- The kernel of a cover is bounded by the dual first cohomology of its quotient. -/
lemma finrank_ker_le_H1_of_cover [Finite G]
    [FiniteDimensional k V] [FiniteDimensional k W]
    (p : σ.IntertwiningMap ρ) (hp : IsCover p) :
    finrank k p.toLinearMap.ker ≤ finrank k (H1 ρ.dual) := by
  have : FiniteDimensional k (Module.Dual k (cocycles ρ.dual)) :=
    Subspace.instModuleDualFiniteDimensional (K := k) (V := cocycles ρ.dual)
  obtain ⟨q, hq, _⟩ := exists_universalCover_quotient p hp
  have hd := LinearMap.finrank_le_finrank_of_surjective hq
  have hu := (universalCoverProjection ρ).toLinearMap.finrank_range_add_finrank_ker
  have hp' := p.toLinearMap.finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (universalCoverProjection ρ).toLinearMap.range
  rw [finrank_ker_universalCoverProjection] at hu
  rw [LinearMap.range_eq_top.mpr hp.1, finrank_top] at hp'
  omega
end Representation.OneCohomology
