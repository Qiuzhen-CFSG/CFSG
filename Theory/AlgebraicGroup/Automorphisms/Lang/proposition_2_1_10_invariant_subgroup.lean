module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_8
public import Theory.AlgebraicGroup.Morphism.IsoImageOfPullbackSurjective

/-!
This module proves the invariant-closed-subgroup restriction in GLS3,
Proposition 2.1.10. The restricted endomorphism is obtained by codomain
restriction. Composing the original Frobenius witness embedding with the
closed-subgroup inclusion gives an embedding into the same general linear
group; surjectivity of coordinate pullbacks identifies the subgroup with its
closed image. Iteration commutes with inclusion, so the original matrix
Frobenius equation proves that the restricted map has the same level.
-/

universe u

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem proposition_2_1_10_invariant_subgroup
    {K : Variety k} [AlgebraicGroup K]
    {r : ℕ} [Fact r.Prime] [CharP k r]
    (σ : AlgebraicGroup.Morphism K K) (q₀ : NNReal)
    (hσ : IsFrobeniusEndomorphismOfLevel (r := r) q₀ σ)
    (H : ClosedSubgroup K)
    (hInv : σ.onPoints '' (H : Set (Variety.Point K)) =
      (H : Set (Variety.Point K))) :
    ∃ τ : AlgebraicGroup.Morphism H.carrierVariety H.carrierVariety,
      IsFrobeniusEndomorphismOfLevel (r := r) q₀ τ ∧
        ∀ x, H.inclusion.onPoints (τ.onPoints x) =
          σ.onPoints (H.inclusion.onPoints x) := by
  letI := H.carrierAlgebraicGroup
  have hmap (x : Variety.Point H.carrierVariety) :
      σ.onPoints (H.inclusion.onPoints x) ∈ H.toSubgroup := by
    change σ.onPoints (H.inclusion.onPoints x) ∈
      (H : Set (Variety.Point K))
    rw [← hInv]
    exact ⟨H.inclusion.onPoints x, (H.pointEquiv x).property, rfl⟩
  let τ := (σ.comp H.inclusion).codRestrictClosedSubgroup H hmap
  have hτ (x : Variety.Point H.carrierVariety) :
      H.inclusion.onPoints (τ.onPoints x) =
        σ.onPoints (H.inclusion.onPoints x) :=
    Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ x
  refine ⟨τ, ?_, hτ⟩
  rcases hσ with ⟨m, a, n, C, hm, ha, hq, e, he⟩
  letI := C.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism H.carrierVariety (glVariety n : Variety k) :=
    C.inclusion.comp (e.hom.comp H.inclusion)
  have hfPull : Function.Surjective f.toVariety.pullbackRingHom := by
    rw [show f.toVariety.pullbackRingHom =
        H.inclusion.toVariety.pullbackRingHom.comp
          (e.hom.toVariety.pullbackRingHom.comp
            C.inclusion.toVariety.pullbackRingHom) from by
      dsimp only [f]
      rw [show (C.inclusion.comp (e.hom.comp H.inclusion)).toVariety =
          C.inclusion.toVariety.comp (e.hom.comp H.inclusion).toVariety from rfl,
        Variety.Morphism.pullbackRingHom_comp]
      rw [show (e.hom.comp H.inclusion).toVariety =
          e.hom.toVariety.comp H.inclusion.toVariety from rfl,
        Variety.Morphism.pullbackRingHom_comp]
      rfl]
    exact H.restrictionRingHom_surjective.comp
      ((algebraicGroupIso_hom_pullbackRingHom_surjective e).comp
        C.restrictionRingHom_surjective)
  let D := f.imageClosedSubgroup
  letI := D.carrierAlgebraicGroup
  obtain ⟨eH, heH⟩ :=
    f.iso_imageClosedSubgroup_of_pullbackRingHom_surjective hfPull
  refine ⟨m, a, n, D, hm, ha, hq, eH, ?_⟩
  intro x
  have hiter (j : ℕ) (y : Variety.Point H.carrierVariety) :
      H.inclusion.onPoints ((τ.onPoints^[j]) y) =
        (σ.onPoints^[j]) (H.inclusion.onPoints y) := by
    induction j generalizing y with
    | zero => rfl
    | succ j ih =>
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
        calc
          H.inclusion.onPoints ((τ.onPoints^[j]) (τ.onPoints y)) =
              (σ.onPoints^[j]) (H.inclusion.onPoints (τ.onPoints y)) :=
            ih (τ.onPoints y)
          _ = (σ.onPoints^[j]) (σ.onPoints (H.inclusion.onPoints y)) := by
            rw [hτ]
  have heH_apply (y : Variety.Point H.carrierVariety) :
      D.inclusion.onPoints (eH.hom.onPoints y) = f.onPoints y := by
    rw [heH]
    exact Morphism.codRestrictClosedSubgroup_inclusion_apply _ _ _ y
  rw [heH_apply, heH_apply]
  change glPointEquiv n
      (C.inclusion.onPoints
        (e.hom.onPoints
          (H.inclusion.onPoints ((τ.onPoints^[m]) x)))) = _
  rw [hiter]
  exact he (H.inclusion.onPoints x)

end Theory.AlgebraicGroup
