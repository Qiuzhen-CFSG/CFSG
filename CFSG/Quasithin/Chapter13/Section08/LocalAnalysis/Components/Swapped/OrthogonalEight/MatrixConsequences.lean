module

public import Theory.Representation.OrthogonalFourPlusMatrix.Normalizer
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.OrthogonalEight.Consequences

/-!
# The determinant-model consequences for 13.8.16

The displacement calculation now supplies the critical-line contradiction and
fixed codimension four for every nontrivial quadratic actor in the actual
SL₂(4) × SL₂(4) determinant action. Linear identifications transport displacement
without changing either the actor or the subspaces.

The separate comparison with the existing Siegel-generated Ω₄⁺(4) carrier and
the upper bound four on quadratic actor orders are still needed for the
orthogonal source-theorem assembly. These are not hypotheses silently folded
into a family label. Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.OrthogonalEight.MatrixConsequences
open Representation.BinaryOffender
open ClassicalOrthogonal.FourPlusMatrix

/-- Nontrivial quadratic subgroups in the determinant model have fixed codimension four. -/
theorem quadratic_fixedCodim_eq_four (A : Subgroup Binary.G) (hne : A ≠ ⊥)
    (hq : IsQuadratic Binary.action A) : fixedCodim Binary.action A = 4 :=
  OrthogonalEight.quadratic_fixedCodim_eq_four Binary.action Binary.finrank_binary A hne hq
    (fun a _ ha => Displacement.displacement_rank_four a ha)

/-- Equivariant coordinates preserve the literal displacement rank. -/
theorem displacement_rank_eq {H W : Type*} [Group H] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) H W)
    (f : H →* Binary.G) (e : W ≃ₗ[ZMod 2] Binary.V)
    (he : ∀ g w, e (ρ g w) = Binary.action (f g) (e w)) (g : H) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) =
      Module.finrank (ZMod 2) (LinearMap.range (Binary.action (f g) - LinearMap.id)) := by
  have hr : (LinearMap.range (ρ g - LinearMap.id)).map e.toLinearMap =
      LinearMap.range (Binary.action (f g) - LinearMap.id) := by
    ext v
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      refine ⟨e w, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub, he]
    · rintro ⟨w, rfl⟩
      refine ⟨(ρ g - (LinearMap.id : W →ₗ[ZMod 2] W)) (e.symm w),
        ⟨e.symm w, rfl⟩, ?_⟩
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub,
        he, LinearEquiv.apply_symm_apply]
  have hd := (Submodule.equivMapOfInjective e.toLinearMap e.injective
    (LinearMap.range (ρ g - LinearMap.id))).finrank_eq
  rwa [hr] at hd

/-- A nonidentity determinant-model actor cannot send a codimension-two
subspace into a displacement line, under any explicit equivariant identification. -/
theorem no_critical_line_of_equivariant_model {H W : Type*} [Group H] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (f : H →* Binary.G)
    (e : W ≃ₗ[ZMod 2] Binary.V)
    (he : ∀ g w, e (ρ g w) = Binary.action (f g) (e w))
    (g : H) (hg : f g ≠ 1) (D S : Submodule (ZMod 2) W)
    (hD : Module.finrank (ZMod 2) (W ⧸ D) ≤ 2)
    (hS : Module.finrank (ZMod 2) S ≤ 1) :
    ¬ ∀ d ∈ D, ρ g d - d ∈ S := by
  apply no_critical_line_of_displacement_rank_four ρ D S g hD hS
  rw [displacement_rank_eq ρ f e he g]
  exact Displacement.displacement_rank_four (f g) hg

/-- A binary action extending a normal determinant-model subgroup has no
transvections. The group isomorphism and module identification are explicit;
no faithfulness or normalizer classification is additionally assumed. -/
theorem equivariant_extension_no_transvection {H W : Type*} [Group H] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : H →* (W ≃ₗ[ZMod 2] W)) (N : Subgroup H) [N.Normal]
    (f : N ≃* Binary.G) (e : W ≃ₗ[ZMod 2] Binary.V)
    (he : ∀ n : N, ∀ w, e (ρ n w) = Binary.action (f n) (e w)) (h : H) :
    Module.finrank (ZMod 2) (LinearMap.range ((ρ h).toLinearMap - LinearMap.id)) ≠ 1 := by
  let σ : Representation (ZMod 2) N W :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (ρ.comp N.subtype)
  apply Representation.BinaryNormalizerRank.normalizer_no_rank_one (N.map ρ)
    (t := ρ h)
  · rintro _ ⟨n, hn, rfl⟩ hne
    have hn1 : f ⟨n, hn⟩ ≠ 1 := by
      intro hh
      have hnp : (⟨n, hn⟩ : N) = 1 := f.injective (hh.trans f.map_one.symm)
      have hn0 : n = 1 := congrArg Subtype.val hnp
      exact hne (hn0 ▸ ρ.map_one)
    have hd := displacement_rank_eq σ f.toMonoidHom e he ⟨n, hn⟩
    change Module.finrank (ZMod 2) (LinearMap.range ((ρ n).toLinearMap - LinearMap.id)) = _ at hd
    change 3 ≤ Module.finrank (ZMod 2) (LinearMap.range ((ρ n).toLinearMap - LinearMap.id))
    exact ((by decide : 3 ≤ 4).trans
      (Displacement.displacement_rank_four _ hn1)).trans_eq hd.symm
  · intro v hv
    apply e.injective
    rw [e.map_zero]
    apply Displacement.common_fixed_eq_zero
    intro g
    obtain ⟨n, rfl⟩ := f.surjective g
    rw [← he]
    exact congrArg e (hv (ρ n) (Subgroup.mem_map_of_mem ρ n.property))
  · apply Subgroup.le_normalizer_map ρ
    apply Subgroup.mem_map_of_mem
    rw [Subgroup.normalizer_eq_top]
    trivial


end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.OrthogonalEight.MatrixConsequences
