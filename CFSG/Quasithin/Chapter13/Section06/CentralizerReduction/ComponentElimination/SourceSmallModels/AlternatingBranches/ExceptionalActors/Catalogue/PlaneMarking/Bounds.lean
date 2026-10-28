module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.Coordinates
public import Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.Geometry
import all Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.Maximality

/-!
# The order of an intrinsic exceptional A₇ plane stabilizer

The actual A₈–GL₄(2) equivalence gives order divisibility by 576 and index
at most 35 for any plane stabilizer in a faithful binary four-space.
Its order also divides 2520, forcing order 72 and index 35.
No classification of faithful modules is assumed.

The coordinate argument is adapted from Section08's FourSpace/Parabolic;
only its lower-layer geometric inputs are imported here, avoiding a cycle.
Source: Aschbacher–Smith, Lemma 13.6.22, printed p.932.
-/

open Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricEight.FourBlockParabolic
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.PlaneMarking
private theorem plane_index : (BinaryLinear.parabolic plane).index = 35 := by
  rw [← Subgroup.index_comap_of_surjective _ (f := equiv.toMonoidHom) equiv.surjective, parabolic_comap]
  exact evenFour_index
private theorem plane_card : Nat.card (BinaryLinear.parabolic plane) = 576 := by
  have hc : Nat.card (BinaryLinear.GL Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.V) = 20160 :=
    (Nat.card_congr equiv.toEquiv).symm.trans alt_card
  have h := (BinaryLinear.parabolic plane).card_mul_index
  rw [plane_index, hc] at h
  omega

private theorem exists_plane_equiv {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (hdim : Module.finrank (ZMod 2) V = 4)
    (S : Submodule (ZMod 2) V) (hS : Module.finrank (ZMod 2) S = 2) :
    ∃ e : V ≃ₗ[ZMod 2] Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.V, ∀ v, e v ∈ plane ↔ v ∈ S := by
  classical
  let e : V ≃ₗ[ZMod 2] Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.V := (Module.finBasisOfFinrankEq (ZMod 2) V hdim).equivFun
  let W := S.map e.toLinearMap
  have hW : Module.finrank (ZMod 2) W = 2 := (e.finrank_map_eq S).trans hS
  let f : W ≃ₗ[ZMod 2] plane := LinearEquiv.ofFinrankEq W plane (hW.trans plane_finrank.symm)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨e.trans g, fun v => ?_⟩
  constructor
  · intro hv
    let w : W := f.symm ⟨(e.trans g) v, hv⟩
    have hw : g (w : Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.V) = g (e v) := (hg w).symm.trans (congrArg Subtype.val (f.apply_symm_apply _))
    have hew : e v ∈ W := g.injective hw ▸ w.property
    obtain ⟨u, hu, he⟩ := hew
    exact e.injective he ▸ hu
  · intro hv
    have hew : e v ∈ W := ⟨v, hv, rfl⟩
    rw [LinearEquiv.trans_apply, ← hg ⟨e v, hew⟩]
    exact (f ⟨e v, hew⟩).property

open LinearMap.GeneralLinearGroup
private theorem exists_action_hom {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) A7 V) (hσ : Function.Injective σ)
    (S : Submodule (ZMod 2) V) (e : V ≃ₗ[ZMod 2] Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.V)
    (he : ∀ v, e v ∈ plane ↔ v ∈ S) :
    ∃ f : A7 →* BinaryLinear.GL Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.V, Function.Injective f ∧
      (BinaryLinear.parabolic plane).comap f = subspaceStabilizer σ S := by
  let f : A7 →* BinaryLinear.GL Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.V :=
    (generalLinearEquiv (ZMod 2) Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.V).toMonoidHom.comp
      ((congrLinearEquiv e).toMonoidHom.comp σ.asGroupHom)
  refine ⟨f, ?_, ?_⟩
  · apply (generalLinearEquiv (ZMod 2) Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.V).injective.comp
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
public theorem planeStabilizer_bounds {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
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

/-- Every plane stabilizer in a faithful binary four-dimensional A₇ action
has order 72 and index 35. -/
public theorem planeStabilizer_card_index {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A7 W) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4)
    (P : Submodule (ZMod 2) W) (hP : Module.finrank (ZMod 2) P = 2) :
    Nat.card (subspaceStabilizer ρ P) = 72 ∧ (subspaceStabilizer ρ P).index = 35 := by
  obtain ⟨hd, hi⟩ := planeStabilizer_bounds ρ hρ hdim P hP
  have ha : Nat.card A7 = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hk := (subspaceStabilizer ρ P).card_subgroup_dvd_card
  rw [ha] at hk
  have hg : Nat.card (subspaceStabilizer ρ P) ∣ 72 := by
    simpa using Nat.dvd_gcd hd hk
  have hle := Nat.le_of_dvd (by decide : 0 < 72) hg
  have hm := (subspaceStabilizer ρ P).card_mul_index
  rw [ha] at hm
  have hbound := Nat.mul_le_mul_left (Nat.card (subspaceStabilizer ρ P)) hi
  rw [hm] at hbound
  have hc : Nat.card (subspaceStabilizer ρ P) = 72 := by omega
  exact ⟨hc, by rw [hc] at hm; omega⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.PlaneMarking
