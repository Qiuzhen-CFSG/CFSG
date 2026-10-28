module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Seven.Inputs
public import Theory.Alternating.IndexEightSubgroups
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Mathlib.LinearAlgebra.Determinant

/-!
# Recognition of the A₇ binary four-space

Choose linear coordinates and identify GL₄(2) with SL₄(2), since every
nonzero binary determinant is one. The actual exceptional SL₄(2)–A₈
comparison sends the component image to an index-eight subgroup. Such a
subgroup equals its normalizer, so normality of L and faithfulness give G = L.
The index-eight conjugacy theorem supplies an even permutation carrying this
image to the literal seven-letter embedding. Its image in SL₄(2), composed
with the chosen coordinates, is the required intertwiner. The resulting
isomorphism of actors allows exactly the automorphism twist of quasiequivalence.

Source: Aschbacher–Smith, K.1.2, printed p.452 (PDF p.463). This proves the
fixed-dimension branch directly; the independent numerical degree assertion
remains with the assembly in `Seven.lean`.
-/

public section

open scoped MatrixGroups
open Representation
namespace CFSG.Quasithin.ChapterK.Alternating
open ChapterB.QuasisimpleSource
open Subgroup
universe u v
open AlternatingSevenConjugatePair.Model
noncomputable section

private def linearEquivToSL (e : Four ≃ₗ[ZMod 2] Four) : SL(4, ZMod 2) :=
  ⟨LinearMap.toMatrix' e.toLinearMap, by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ e.isUnit_det'.ne_zero⟩

private theorem linearEquivToSL_apply (e : Four ≃ₗ[ZMod 2] Four) :
    Matrix.SpecialLinearGroup.toLin' (linearEquivToSL e) = e := by
  apply LinearEquiv.toLinearMap_injective
  exact Matrix.toLin'_toMatrix' e.toLinearMap

private def linearEquivToSLHom : (Four ≃ₗ[ZMod 2] Four) →* SL(4, ZMod 2) where
  toFun := linearEquivToSL
  map_one' := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [linearEquivToSL_apply, map_one]
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.toLin'_injective
    rw [map_mul, linearEquivToSL_apply, linearEquivToSL_apply, linearEquivToSL_apply]

private def comparison : alternatingGroup (Fin 8) ≃* SL(4, ZMod 2) :=
  Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    Atlas.Order20160A8.sl4TwoEquivPSL.symm

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private def coordinateAction (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) : Representation (ZMod 2) G Four :=
  b.conjRingEquiv.toMonoidHom.comp ρ

private def linearImage (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) : G →* SL(4, ZMod 2) :=
  linearEquivToSLHom.comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Four).toMonoidHom.comp
      (coordinateAction ρ b).asGroupHom)

private theorem linearImage_apply (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) (g : G) (v : V) :
    Matrix.SpecialLinearGroup.toLin' (linearImage ρ b g) (b v) = b (ρ g v) := by
  rw [show linearImage ρ b g = linearEquivToSL
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Four
      ((coordinateAction ρ b).asGroupHom g)) from rfl, linearEquivToSL_apply]
  change b (ρ g (b.symm (b v))) = _
  rw [b.symm_apply_apply]

private theorem linearImage_injective (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) (hf : Function.Injective ρ) :
    Function.Injective (linearImage ρ b) := by
  intro g h he
  apply hf
  ext v
  apply b.injective
  rw [← linearImage_apply ρ b g, ← linearImage_apply ρ b h, he]

private def permutationImage (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) : G →* alternatingGroup (Fin 8) :=
  comparison.symm.toMonoidHom.comp (linearImage ρ b)

private theorem permutationImage_injective (ρ : Representation (ZMod 2) G V)
    (b : V ≃ₗ[ZMod 2] Four) (hf : Function.Injective ρ) :
    Function.Injective (permutationImage ρ b) :=
  comparison.symm.injective.comp (linearImage_injective ρ b hf)


/-- The faithful A₇ four-space is the restricted SL₄(2) model, and admits no
proper faithful ambient extension with normal component. -/
theorem sevenFourSpace : RecognitionInputs.Seven.FourSpace.{u,v} := by
  intro G V _ _ _ _ _ ρ K L h eL hd
  classical
  obtain ⟨b⟩ : Nonempty (V ≃ₗ[ZMod 2] Four) :=
    FiniteDimensional.nonempty_linearEquiv_of_finrank_eq (hd.trans four_dimension.symm)
  let f := permutationImage ρ b
  have hf : Function.Injective f := permutationImage_injective ρ b h.faithful
  let H := L.map f
  have hcard : Nat.card H = 2520 := by
    rw [← Nat.card_congr (L.equivMapOfInjective f hf).toEquiv,
      Nat.card_congr eL.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hA : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hindex : H.index = 8 := by
    have hh := H.card_mul_index
    rw [hcard, hA] at hh
    omega
  -- The source supplies actual normality through its intrinsic F*(G).
  let : L.Normal := by rw [h.fitting]; infer_instance
  have hn (g : G) : f g ∈ normalizer (H : Set (alternatingGroup (Fin 8))) := by
    apply Subgroup.le_normalizer_map (H := L) f
    exact ⟨g, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩
  have hwhole : L = ⊤ := by
    apply top_unique
    intro g _
    have hg : f g ∈ H := by
      rw [← GroupTheory.AlternatingIndexEight.index_eight_normalizer H hindex]
      exact hn g
    exact (Subgroup.mem_map_iff_mem hf).mp hg
  refine ⟨hwhole, ?_⟩
  let J := alternatingEmbedding.range
  have hJcard : Nat.card J = 2520 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective alternatingEmbedding_injective).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hJindex : J.index = 8 := by
    have hh := J.card_mul_index
    rw [hJcard, hA] at hh
    omega
  -- Conjugacy takes place inside A₈, so it lifts to a linear coordinate change.
  obtain ⟨c, hc⟩ := GroupTheory.AlternatingIndexEight.index_eight_conjugate
    H J hindex hJindex
  let q := (MulAut.conj c).toMonoidHom.comp (f.comp L.subtype)
  have hq : Function.Injective q := (MulAut.conj c).injective.comp
    (hf.comp L.subtype_injective)
  have hqr : q.range = alternatingEmbedding.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype]
    exact hc
  let eGroup : L ≃* alternatingGroup (Fin 7) :=
    (MonoidHom.ofInjective hq).trans ((MulEquiv.subgroupCongr hqr).trans
      (MonoidHom.ofInjective alternatingEmbedding_injective).symm)
  have he (l : L) : alternatingEmbedding (eGroup l) = q l := by
    exact congrArg Subtype.val
      ((MonoidHom.ofInjective alternatingEmbedding_injective).apply_symm_apply
        ((MulEquiv.subgroupCongr hqr) ((MonoidHom.ofInjective hq) l)))
  let t : Four ≃ₗ[ZMod 2] Four := Matrix.SpecialLinearGroup.toLin' (comparison c)
  refine ⟨⟨eGroup, b.trans t, fun l v => ?_⟩⟩
  have hlin : linearEmbedding (eGroup l) =
      comparison c * linearImage ρ b l.val * (comparison c)⁻¹ := by
    change comparison (alternatingEmbedding (eGroup l)) = _
    rw [he]
    change comparison (c * (comparison.symm (linearImage ρ b l.val)) * c⁻¹) = _
    rw [map_mul, map_mul, map_inv, comparison.apply_symm_apply]
  change t (b (ρ l.val v)) =
    Matrix.SpecialLinearGroup.toLin' (linearEmbedding (eGroup l)) (t (b v))
  rw [hlin, map_mul, map_mul, map_inv]
  change t (b (ρ l.val v)) = t
    (Matrix.SpecialLinearGroup.toLin' (linearImage ρ b l.val) (t.symm (t (b v))))
  rw [t.symm_apply_apply, linearImage_apply]

end
end CFSG.Quasithin.ChapterK.Alternating
