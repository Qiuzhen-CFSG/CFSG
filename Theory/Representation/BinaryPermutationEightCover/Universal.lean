module

public import Theory.Representation.BinaryPermutationNaturalCover

/-!
# Universal recognition of the eight-letter augmentation cover

The universal perfect cover maps onto the core. Rank-nullity and the
one-dimensional dual H¹ make this map an isomorphism. Every perfect central
cover is consequently a quotient of the core over the literal natural map.

Source: Aschbacher–Smith, B.3.2, printed pp.83–84, and I.1.5–6, printed p.408.
The consumer is the central extension in 13.5.21(6), printed p.924.
-/

@[expose] public section
open Representation Representation.OneCohomology
namespace BinaryPermutation.EightCover
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

private lemma universal_finrank_formula {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (τ : Representation (ZMod 2) G V)
    (hsur : Function.Surjective (universalCoverProjection τ)) :
    Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (cocycles τ.dual)) =
      Module.finrank (ZMod 2) V + Module.finrank (ZMod 2) (H1 τ.dual) := by
  have hu := (universalCoverProjection τ).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsur, finrank_top,
    finrank_ker_universalCoverProjection] at hu
  exact hu.symm

private lemma universal_finrank
    (hsur : Function.Surjective
      (universalCoverProjection (alternatingNaturalRepresentation (Fin 8)))) :
    Module.finrank (ZMod 2) (Module.Dual (ZMod 2)
      (cocycles (alternatingNaturalRepresentation (Fin 8)).dual)) =
      Module.finrank (ZMod 2) (core (Fin 8)) := by
  rw [universal_finrank_formula _ hsur, finrank_natural_even (Fin 8) (by decide),
    alternatingEight_natural_dual_finrank_H1, finrank_core]
  norm_num

private lemma universal_core_map :
    ∃ b : (universalAction (alternatingNaturalRepresentation (Fin 8)).dual).dual.IntertwiningMap
        (alternatingCoreRepresentation (Fin 8)),
      Function.Bijective b ∧ ∀ u,
        coreToNatural (Fin 8) (b u) = universalCoverProjection (alternatingNaturalRepresentation (Fin 8)) u := by
  obtain ⟨b, hb, hbq⟩ := exists_universalCover_quotient
    (alternatingCoreProjection (Fin 8)) alternatingEight_coreProjection_isCover
  have hsurU : Function.Surjective (universalCoverProjection (alternatingNaturalRepresentation (Fin 8))) := by
    intro v
    obtain ⟨w, rfl⟩ := coreToNatural_surjective v
    obtain ⟨x, rfl⟩ := hb w
    exact ⟨x, (hbq x).symm⟩
  have hbfin := universal_finrank hsurU
  exact ⟨b, ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hbfin).mpr hb, hb⟩, hbq⟩

/-- Every perfect central cover receives a surjection from the core over the natural projection. -/
lemma core_quotient_of_alternating_cover
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 8)) U)
    (P : σ.IntertwiningMap (alternatingNaturalRepresentation (Fin 8))) (hP : IsCover P) :
    ∃ f : core (Fin 8) →ₗ[ZMod 2] U, Function.Surjective f ∧
      (∀ g : alternatingGroup (Fin 8), ∀ v,
        f (coreRepresentation (Fin 8) g.val v) = σ g (f v)) ∧
      ∀ v, P (f v) = coreToNatural (Fin 8) v := by
  obtain ⟨b, hb, hbq⟩ := universal_core_map
  obtain ⟨c, hc, hcp⟩ := exists_universalCover_quotient P hP
  let B := LinearEquiv.ofBijective b.toLinearMap hb
  let f : core (Fin 8) →ₗ[ZMod 2] U := c.toLinearMap.comp B.symm.toLinearMap
  have hf : Function.Surjective f := hc.comp B.symm.surjective
  have hpf (v : core (Fin 8)) : P (f v) = coreToNatural (Fin 8) v := by
    change P (c (B.symm v)) = _
    rw [hcp, ← hbq]
    change coreToNatural (Fin 8) (B (B.symm v)) = _
    rw [B.apply_symm_apply]
  have hfa (g : alternatingGroup (Fin 8)) (v : core (Fin 8)) :
      f (coreRepresentation (Fin 8) g.val v) = σ g (f v) := by
    have he : B.symm (coreRepresentation (Fin 8) g.val v) =
        (universalAction (alternatingNaturalRepresentation (Fin 8)).dual).dual g (B.symm v) := by
      apply B.injective
      rw [B.apply_symm_apply]
      exact (congrArg (coreRepresentation (Fin 8) g.val) (B.apply_symm_apply v)).symm.trans
        (LinearMap.congr_fun (b.isIntertwining' g) (B.symm v)).symm
    change c (B.symm _) = σ g (c (B.symm v))
    rw [he]
    exact LinearMap.congr_fun (c.isIntertwining' g) (B.symm v)
  exact ⟨f, hf, hfa, hpf⟩

end BinaryPermutation.EightCover
