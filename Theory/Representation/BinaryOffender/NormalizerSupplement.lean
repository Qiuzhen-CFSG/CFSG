module
public import Theory.Representation.BinaryNormalizerResidual
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Sylow supplements from a marked linear normalizer

Conjugate the original action through the module marking. Its normal
subgroup has exactly the model action image, so the whole actor maps to
the model normalizer. A bound on that normalizer's two-residual places
the original residual in the component times the full action kernel.
Sylow supplementation then gives the whole group. No faithfulness of the
original action or replacement of its kernel by a two-core is required.

Source application: Aschbacher–Smith 13.4.7(2), printed p.902.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryOffender
variable {H B M V : Type*} [Group H] [Finite H] [Group B]
  [AddCommGroup M] [Module (ZMod 2) M] [AddCommGroup V] [Module (ZMod 2) V]

/-- A normal component whose model normalizer has no new two-residual
supplements the full action kernel together with a Sylow two-subgroup. -/
theorem sylow_supplement_of_model_normalizer
    (ρ : Representation (ZMod 2) H V) (K : Subgroup H) [K.Normal]
    (S : Sylow 2 H) (f : K →* B) (hf : Function.Surjective f)
    (σ : Representation (ZMod 2) B M) (e : M ≃ₗ[ZMod 2] V)
    (he : ∀ k v, e (σ (f k) v) = ρ k (e v))
    (hmodel : (pResidual 2 (linearNormalizer σ)).map (linearNormalizer σ).subtype ≤
      actionImage σ) :
    (K ⊔ ρ.asGroupHom.ker) ⊔ (S : Subgroup H) = ⊤ := by
  let a := (BinaryNormalizerResidual.unitConj e.symm).toMonoidHom.comp ρ.asGroupHom
  have hm : K.map a = actionImage σ := by
    ext x
    constructor
    · rintro ⟨k,hk,rfl⟩
      refine ⟨f ⟨k,hk⟩,?_⟩
      apply Units.ext
      apply LinearMap.ext
      intro v
      change σ (f ⟨k,hk⟩) v = e.symm (ρ k (e v))
      exact (e.symm_apply_eq.mpr (he ⟨k,hk⟩ v).symm).symm
    · rintro ⟨b,rfl⟩
      obtain ⟨k,rfl⟩ := hf b
      refine ⟨k,k.property,?_⟩
      apply Units.ext
      apply LinearMap.ext
      intro v
      change e.symm (ρ k.val (e v)) = σ (f k) v
      exact e.symm_apply_eq.mpr (he k v).symm
  have hn (g : H) : a g ∈ linearNormalizer σ := by
    change a g ∈ normalizer (actionImage σ : Set _)
    rw [←hm]
    exact K.le_normalizer_map a (mem_map_of_mem a
      (show g ∈ normalizer (K : Set H) from le_normalizer_of_normal (mem_top g)))
  let b : H →* linearNormalizer σ := a.codRestrict _ hn
  have hr : (pResidual 2 H).map a ≤ K.map a := by
    rw [hm]
    intro x hx
    obtain ⟨g,hg,rfl⟩ := hx
    exact hmodel (mem_map_of_mem (linearNormalizer σ).subtype
      (map_pResidual_le 2 b (mem_map_of_mem b hg)))
  have hk : a.ker = ρ.asGroupHom.ker :=
    MonoidHom.ker_comp_of_injective _ _ (BinaryNormalizerResidual.unitConj e.symm).injective
  have hle : pResidual 2 H ≤ K ⊔ ρ.asGroupHom.ker := by
    rw [←hk,←comap_map_eq]
    exact (le_comap_map a _).trans (comap_mono hr)
  apply top_unique
  rw [←pResidual_sup_sylow_eq_top S]
  exact sup_le_sup_right hle _
end Representation.BinaryOffender
