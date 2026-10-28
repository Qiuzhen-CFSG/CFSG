module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.Models
public import Theory.Representation.SL2NaturalOffenders.NoStrong
public import Theory.Representation.SpecialLinearNatural.CubicFixedSpace
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five

/-!
# Bounds for the concrete rank-one models

This file contains only the model calculation used by the action-image
bootstrap.  The actor equivalences in `RankOneModel` are retained literally;
in particular, all central kernels and both extension orientations in a
`ModelSection` remain present.  The SL₂ estimate is the fixed-vector estimate
for a natural section.  In the SL₃ and S₅ cases the explicit cubic is lifted
through that section and then conjugated to the supplied ambient Sylow
subgroup.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.5.1,
printed p.99, and the proof of 15.3.67, printed pp.1153--1154.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer

universe u v w

variable {D N : Type u} [Group D] [Finite D] [Group N] [Finite N]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

omit [Finite N] in
private theorem noStrong_of_linearTwo_section
    (σ : Representation (ZMod 2) N W) (F : BinaryField)
    (actor : N ≃* Matrix.SpecialLinearGroup (Fin 2) F.Carrier)
    (s : ModelSection σ actor.symm.toMonoidHom (linearNatural F 2)) :
    ¬ IsStrongFFModule σ := by
  let τ := σ.comp actor.symm.toMonoidHom
  have hτ : ¬ IsStrongFFModule τ :=
    Representation.SL2NaturalOffenders.NoStrong.not_strong_of_natural_section τ
      (MonoidHom.id _) (fun _ _ h => h) s.space s.projection s.surjective s.intertwines
  have he (g : N) (v : W) :
      (LinearEquiv.refl (ZMod 2) W) (σ g v) =
        τ (actor.toMonoidHom g) ((LinearEquiv.refl (ZMod 2) W) v) := by
    change σ g v = σ (actor.symm (actor g)) v
    rw [actor.symm_apply_apply]
  rintro ⟨A, hA⟩
  have hm := (IsOffender.map_equivariant σ τ actor.toMonoidHom actor.injective
    (LinearEquiv.refl (ZMod 2) W) he ⟨hA.1, hA.2.le⟩).1
  apply hτ ⟨A.map actor.toMonoidHom, hm, ?_⟩
  rw [← fixedCodim_map_equivariant σ τ actor.toMonoidHom
    (LinearEquiv.refl (ZMod 2) W) he,
    rank_map_injective actor.toMonoidHom actor.injective]
  exact hA.2

private theorem repeated_cycle_fixes
    (F : BinaryField) {r : ℕ}
    :
    ∀ v ∈ fixedSpace (repeated (linearNatural F 3) r)
      (Representation.SL3BinaryCubic.klein (F := F.Carrier)),
      repeated (linearNatural F 3) r
        (Representation.SL3BinaryCubic.cycle (F := F.Carrier)) v = v := by
  intro v hv
  funext i
  change Representation.SL3BinaryCubic.natural
      (Representation.SL3BinaryCubic.cycle (F := F.Carrier)) (v i) = v i
  apply Representation.SL3BinaryCubic.cycle_fixes_natural
  intro g
  have h := congrFun (hv g) i
  exact h

omit [Finite N] [FiniteDimensional (ZMod 2) W] in
private theorem model_cubic_of_linearThree
    (F : BinaryField)
    (ρ : Representation (ZMod 2) D W)
    (f : N →* D) (hf : Function.Injective f)
    (actor : N ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (copies : ℕ) (_hcopies : copies = 1 ∨ copies = 2)
    (s : ModelSection (ρ.comp f) actor.symm.toMonoidHom
      (repeated (linearNatural F 3) copies))
    (S : Sylow 2 D) :
    ∃ c : D, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v := by
  let A := Representation.SL3BinaryCubic.klein (F := F.Carrier)
  let d := Representation.SL3BinaryCubic.cycle (F := F.Carrier)
  have hfix : ∀ v ∈ fixedSpace (repeated (linearNatural F 3) copies) A,
      repeated (linearNatural F 3) copies d v = v := by
    exact repeated_cycle_fixes F (r := copies)
  have hcentral : ∀ v ∈ fixedSpace
      ((ρ.comp f).comp actor.symm.toMonoidHom) A,
      ((ρ.comp f).comp actor.symm.toMonoidHom) d v = v := by
    exact cubic_fixedSpace_of_central_section
      ((ρ.comp f).comp actor.symm.toMonoidHom)
      (repeated (linearNatural F 3) copies) A d
      Representation.SL3BinaryCubic.cycle_pow
      Representation.SL3BinaryCubic.cycle_normalizes s.space s.projection
      s.intertwines s.kernel_fixed s.quotient_trivial hfix
  exact sylow_fixedSpace_enlargement_of_embedded_cubic ρ
    (f.comp actor.symm.toMonoidHom) (hf.comp actor.symm.injective)
    A Representation.SL3BinaryCubic.klein_two d
    Representation.SL3BinaryCubic.cycle_pow
    Representation.SL3BinaryCubic.cycle_ne_one hcentral S

omit [Finite N] [FiniteDimensional (ZMod 2) W] in
private theorem model_cubic_of_symmetricFive
    (ρ : Representation (ZMod 2) D W)
    (f : N →* D) (hf : Function.Injective f)
    (actor : N ≃* Equiv.Perm (Fin 5))
    (s : ModelSection (ρ.comp f)
      (actor.symm.toMonoidHom.comp (alternatingGroup (Fin 5)).subtype)
      (alternatingNatural 5)) (S : Sylow 2 D) :
    ∃ c : D, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v := by
  let j : alternatingGroup (Fin 5) →* D :=
    f.comp (actor.symm.toMonoidHom.comp (alternatingGroup (Fin 5)).subtype)
  have hj : Function.Injective j := by
    intro a b hab
    apply (alternatingGroup (Fin 5)).subtype_injective
    exact actor.symm.injective (hf hab)
  exact BinaryPermutation.CubicFixedSpace.Five.centralSection_enlargement ρ j hj
    s.space s.projection s.intertwines s.kernel_fixed s.quotient_trivial S

omit [Finite N] in
theorem ambient_model_alternative
    (ρ : Representation (ZMod 2) D W)
    (f : N →* D) (hf : Function.Injective f)
    (hmodel : RankOneModel (ρ.comp f)) (S : Sylow 2 D) :
    ¬ IsStrongFFModule (ρ.comp f) ∨
      ∃ c : D, c ∉ S ∧ c ^ 3 = 1 ∧
        ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v := by
  cases hmodel with
  | linearTwo F actor s =>
      exact Or.inl (noStrong_of_linearTwo_section (ρ.comp f) F actor s)
  | symmetricFive actor s =>
      exact Or.inr (model_cubic_of_symmetricFive ρ f hf actor s S)
  | linearThree F _ copies hcopies actor s =>
      exact Or.inr (model_cubic_of_linearThree F ρ f hf actor copies hcopies s S)

theorem offenderSubgroup_model_alternative
    (ρ : Representation (ZMod 2) D W)
    (hmodel : RankOneModel
      (ρ.comp (offenderSubgroup ρ).subtype)) (S : Sylow 2 D) :
    ¬ IsStrongFFModule (ρ.comp (offenderSubgroup ρ).subtype) ∨
      ∃ c : D, c ∉ S ∧ c ^ 3 = 1 ∧
        ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v :=
  ambient_model_alternative ρ (offenderSubgroup ρ).subtype
    (Subgroup.subtype_injective _) hmodel S

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
