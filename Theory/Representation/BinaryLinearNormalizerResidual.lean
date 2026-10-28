module
public import Theory.Representation.BinaryNormalizerResidual
public import Theory.Representation.GeneralLinearNatural
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorNormalizer
public import Theory.Representation.Quotient
/-!
# Residual bounds for the binary linear small-plane models

The natural SLₙ(2) image is the whole general linear group, because every
invertible binary matrix has determinant one. Its full linear normalizer
therefore contributes no operators beyond the image. The exterior-square
and exterior-cube models for SL₅(2) are self-normalizing. The exhaustive
classification of irreducible ten-dimensional modules supplies one of these
models, so the dimension-only source row has the same residual bound.

The marked-natural and ten-dimensional endpoints retain the literal action
image and normalizer required by the original 13.7.6 source consumer.
Source: Aschbacher–Smith, 13.7.6, printed p.940, and B.4.2's linear and
exterior rows, printed pp.85–86.
-/

public section
namespace Representation.BinaryLinearNormalizerResidual
open Subgroup BinaryOffender BinaryNormalizerResidual
open scoped MatrixGroups

theorem natural_image_eq_top (n : ℕ) :
    actionImage (specialLinearNatural (k := ZMod 2) n) = ⊤ := by
  apply MonoidHom.range_eq_top.mpr
  intro u
  let E := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2)
  obtain ⟨g, hg⟩ := (BinaryLinear.OuterCyclic.slEquivLinear n).surjective (E u)
  refine ⟨g, ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro v
  exact LinearEquiv.congr_fun hg v

theorem natural_residual_le (n : ℕ) :
    (pResidual 2 (linearNormalizer (specialLinearNatural (k := ZMod 2) n))).map
        (linearNormalizer (specialLinearNatural (k := ZMod 2) n)).subtype ≤
      actionImage (specialLinearNatural (k := ZMod 2) n) := by
  rw [natural_image_eq_top]
  exact le_top

theorem exterior_residual_le (r : ℕ) (hr : r = 2 ∨ r = 3) :
    (pResidual 2 (linearNormalizer (SL5TenDimensional.exteriorAction r))).map
        (linearNormalizer (SL5TenDimensional.exteriorAction r)).subtype ≤
      actionImage (SL5TenDimensional.exteriorAction r) :=
  residual_le_of_normalizer_eq _ (SL5TenDimensional.ExteriorNormalizer.normalizer_eq_self r hr)

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem marked_natural_residual_le (n : ℕ)
    (e : G ≃* SL(n, ZMod 2)) (E : V ≃ₗ[ZMod 2] (Fin n → ZMod 2))
    (hE : ∀ g v, E (ρ g v) = specialLinearNatural n (e g) (E v)) :
    (pResidual 2 (linearNormalizer ρ)).map (linearNormalizer ρ).subtype ≤ actionImage ρ :=
  residual_le_of_equiv ρ _ e E hE (natural_residual_le n)

theorem ten_dimensional_residual_le [IsIrreducible ρ]
    (e : G ≃* SL(5, ZMod 2)) (hdim : Module.finrank (ZMod 2) V = 10) :
    (pResidual 2 (linearNormalizer ρ)).map (linearNormalizer ρ).subtype ≤ actionImage ρ := by
  let σ := ρ.comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr inferInstance
  have hb : (pResidual 2 (linearNormalizer σ)).map (linearNormalizer σ).subtype ≤
      actionImage σ := by
    rcases SL5TenDimensional.Classification.identification_of_finrank_ten σ hdim with hh | hh
    · obtain ⟨E⟩ := hh
      exact residual_le_of_equiv σ _ (MulEquiv.refl _) E.toLinearEquiv
        (fun g v => DFunLike.congr_fun (E.toIntertwiningMap.isIntertwining' g) v)
        (exterior_residual_le 2 (Or.inl rfl))
    · obtain ⟨E⟩ := hh
      exact residual_le_of_equiv σ _ (MulEquiv.refl _) E.toLinearEquiv
        (fun g v => DFunLike.congr_fun (E.toIntertwiningMap.isIntertwining' g) v)
        (exterior_residual_le 3 (Or.inr rfl))
  exact residual_le_of_equiv ρ σ e (LinearEquiv.refl (ZMod 2) V)
    (fun g v => by change ρ g v = ρ (e.symm (e g)) v; rw [e.symm_apply_apply]) hb
end Representation.BinaryLinearNormalizerResidual
