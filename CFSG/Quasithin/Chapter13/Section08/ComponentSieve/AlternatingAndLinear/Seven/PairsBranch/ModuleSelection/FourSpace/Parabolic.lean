module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection.Basic
public import Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.Geometry
import all Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.Maximality
open Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection
open Theory.SpecificGroups.SymmetricEight.FourBlockParabolic
/-!
# Orders and indices for the plane stabilizer

An arbitrary binary four-space with a marked plane can be put in coordinates
by extending an equivalence of subspaces. The existing A₈–GL₄(2) equivalence
then identifies its stabilizer with the even four-plus-four partition subgroup,
which has order 576 and index 35. Pulling back along a faithful action gives
order divisibility and an index bound without classifying that action.

The internal import deliberately reuses the index calculation inside the
existing parabolic maximality proof, without changing that shared module's
public boundary. The exported result mentions only the original representation
and its actual subspace stabilizer.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.8.24,
printed p.959/PDF p.976; the exceptional equivalence and marked parabolic
are supplied by `Theory.SpecificGroups.SymmetricEight.FourBlockParabolic`.
-/
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection.FourSpace
private theorem plane_index : (BinaryLinear.parabolic plane).index = 35 := by
  rw [← Subgroup.index_comap_of_surjective _ (f := equiv.toMonoidHom) equiv.surjective, parabolic_comap]
  exact evenFour_index
private theorem plane_card : Nat.card (BinaryLinear.parabolic plane) = 576 := by
  have hc : Nat.card (BinaryLinear.GL Four) = 20160 :=
    (Nat.card_congr equiv.toEquiv).symm.trans alt_card
  have h := (BinaryLinear.parabolic plane).card_mul_index
  rw [plane_index, hc] at h
  omega

private theorem exists_plane_equiv {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hdim : Module.finrank (ZMod 2) V = 4)
    (S : Submodule (ZMod 2) V) (hS : Module.finrank (ZMod 2) S = 2) :
    ∃ e : V ≃ₗ[ZMod 2] Four, ∀ v, e v ∈ plane ↔ v ∈ S := by
  classical
  let e : V ≃ₗ[ZMod 2] Four := (Module.finBasisOfFinrankEq (ZMod 2) V hdim).equivFun
  let W := S.map e.toLinearMap
  have hW : Module.finrank (ZMod 2) W = 2 := (e.finrank_map_eq S).trans hS
  let f : W ≃ₗ[ZMod 2] plane := LinearEquiv.ofFinrankEq W plane (hW.trans plane_finrank.symm)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨e.trans g, fun v => ?_⟩
  constructor
  · intro hv
    let w : W := f.symm ⟨(e.trans g) v, hv⟩
    have hw : g (w : Four) = g (e v) := (hg w).symm.trans (congrArg Subtype.val (f.apply_symm_apply _))
    have hew : e v ∈ W := g.injective hw ▸ w.property
    obtain ⟨u, hu, he⟩ := hew
    exact e.injective he ▸ hu
  · intro hv
    have hew : e v ∈ W := ⟨v, hv, rfl⟩
    rw [LinearEquiv.trans_apply, ← hg ⟨e v, hew⟩]
    exact (f ⟨e v, hew⟩).property

open LinearMap.GeneralLinearGroup
private theorem exists_action_hom {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) A7 V) (hσ : Function.Injective σ)
    (S : Submodule (ZMod 2) V) (e : V ≃ₗ[ZMod 2] Four)
    (he : ∀ v, e v ∈ plane ↔ v ∈ S) :
    ∃ f : A7 →* BinaryLinear.GL Four, Function.Injective f ∧
      (BinaryLinear.parabolic plane).comap f = subspaceStabilizer σ S := by
  let f : A7 →* BinaryLinear.GL Four :=
    (generalLinearEquiv (ZMod 2) Four).toMonoidHom.comp
      ((congrLinearEquiv e).toMonoidHom.comp σ.asGroupHom)
  refine ⟨f, ?_, ?_⟩
  · apply (generalLinearEquiv (ZMod 2) Four).injective.comp
    apply (congrLinearEquiv e).injective.comp
    intro a b h
    exact hσ (congrArg Units.val h)
  · ext a
    change (∀ v, e (σ a (e.symm v)) ∈ plane ↔ v ∈ plane) ↔
      (∀ v, σ a v ∈ S ↔ v ∈ S)
    constructor
    · intro h v
      have hh := h (e v)
      simpa only [e.symm_apply_apply, he] using hh
    · intro h v
      rw [he, h, ← he, e.apply_symm_apply]

/-- Bounds for the full stabilizer of any plane in any faithful binary
four-dimensional A₇ action. -/
public theorem planeStabilizer_bounds {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) A7 V) (hσ : Function.Injective σ)
    (hdim : Module.finrank (ZMod 2) V = 4)
    (S : Submodule (ZMod 2) V) (hS : Module.finrank (ZMod 2) S = 2) :
    Nat.card (subspaceStabilizer σ S) ∣ 576 ∧ (subspaceStabilizer σ S).index ≤ 35 := by
  obtain ⟨e, he⟩ := exists_plane_equiv hdim S hS
  obtain ⟨f, hf, hstab⟩ := exists_action_hom σ hσ S e he
  rw [← hstab]
  constructor
  · rw [← plane_card]
    exact Subgroup.card_comap_dvd_of_injective _ f hf
  · rw [Subgroup.index_comap]
    have h := Subgroup.relIndex_le_of_le_right (H := BinaryLinear.parabolic plane)
      (K := f.range) (L := ⊤) le_top (by simp [plane_index])
    simpa only [Subgroup.relIndex_top_right, plane_index] using h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.ModuleSelection.FourSpace
