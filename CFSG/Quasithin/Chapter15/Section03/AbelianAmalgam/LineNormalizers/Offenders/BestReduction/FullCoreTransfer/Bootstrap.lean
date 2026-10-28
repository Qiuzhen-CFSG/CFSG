module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer
public import Theory.Representation.BinaryOffender.GeneratedCore
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.CoreInput
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.ActionImage
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.TemporaryMarker

/-!
# The conditional return from the faithful action image to the same actor

Strong replacement first transfers a model estimate from J(D,W) to D. The
odd action kernel then transfers it to I. The original maximum images are
ordinary offenders, hence best by B.1.4(6), and generate exactly the original
Thompson image I by the unchanged maximum-family theorem.

The no-strong premise is an explicit intermediate obligation, to be discharged
by full B.5.6/B.5.1 case analysis in this task. This file does not assert that
classification, or the source theorem, is complete.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.1.4(4),(6),
printed p.68, and the proof of 15.3.67, pp.1153–1154.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
variable {G H W : Type*} [Group G] [Group H] [Finite G] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

omit [Finite G] in
/-- The bootstrap closes on the same Thompson actor, once the proper normal
best-offender subgroup of its action image has the model no-strong bound. -/
theorem thompson_image_generated_of_actionImage_core_bound
    (C : Subgroup G) (q : G →* H) (σ : Representation (ZMod 2) H W)
    (hodd : Odd (Nat.card (actionHom
      (σ.comp ((Stellmacher.elementaryAbelianMaxJ C).map q).subtype)).ker))
    (hordinary : ∀ A ∈ Stellmacher.elementaryAbelianMaxSubgroups C,
      A.map q ≠ ⊥ → IsOffender σ (A.map q))
    (hcore : let ρ := σ.comp ((Stellmacher.elementaryAbelianMaxJ C).map q).subtype
      let δ := imageRepresentation ρ
      ¬ IsStrongFFModule (δ.comp (offenderSubgroup δ).subtype)) :
    offenderSubgroup (σ.comp ((Stellmacher.elementaryAbelianMaxJ C).map q).subtype) = ⊤ := by
  let I := (Stellmacher.elementaryAbelianMaxJ C).map q
  let ρ := σ.comp I.subtype
  have hn : ¬ IsStrongFFModule ρ := not_strong_of_odd_action_kernel ρ hodd
    (not_strong_of_offenderSubgroup (imageRepresentation ρ) hcore)
  apply thompson_image_generated_of_maximum_images_best C q σ
  intro A hA hne
  have hAI : A.map q ≤ I := map_mono (le_sSup hA)
  have ho := (hordinary A hA hne).subgroupOf σ hAI
  have hb := ho.isBest_of_not_strong ρ hn
  simpa only [map_subgroupOf_eq_of_le hAI] using hb.map_subtype σ

/-- Consumer on the literal temporary centralizer, full core quotient, and
same `thompsonImage`; no replacement of I by its action image is made. -/
theorem temporary_generated_of_actionImage_core_bound
    (T V E : Subgroup G)
    (σ : Representation (ZMod 2)
      ((temporaryLineNormalizer T V E) ⧸ Replacement.Transvections.localCore T V E) W)
    (hodd : Odd (Nat.card (actionHom (σ.comp (thompsonImage T V E).subtype)).ker))
    (hordinary : ∀ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (localCentralizer T V E),
      A.map (QuotientGroup.mk' (Replacement.Transvections.localCore T V E)) ≠ ⊥ →
        IsOffender σ (A.map (QuotientGroup.mk' (Replacement.Transvections.localCore T V E))))
    (hcore : let δ := imageRepresentation (σ.comp (thompsonImage T V E).subtype)
      ¬ IsStrongFFModule (δ.comp (offenderSubgroup δ).subtype)) :
    offenderSubgroup (σ.comp (thompsonImage T V E).subtype) = ⊤ :=
  thompson_image_generated_of_actionImage_core_bound (localCentralizer T V E)
    (QuotientGroup.mk' (Replacement.Transvections.localCore T V E)) σ hodd hordinary hcore

/-- The source kernel comparison discharges the odd-kernel premise in the
same-I bootstrap. Only the still-open classification/model bound remains. -/
theorem temporary_generated_of_local_kernel_and_core_bound
    (Y T V E : Subgroup G) [IsMulCommutative V]
    (d : Replacement.Transvections.TemporaryData Y T V E)
    (σ : Representation (ZMod 2)
      ((temporaryLineNormalizer T V E) ⧸ Replacement.Transvections.localCore T V E) W)
    (hker : (σ.comp ((QuotientGroup.mk' (Replacement.Transvections.localCore T V E)).comp
        (localCentralizer T V E).subtype)).ker =
      ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
        (localCentralizer T V E))
    (S : Sylow 2 ((localCentralizer T V E).map
      (QuotientGroup.mk' (Replacement.Transvections.localCore T V E))))
    (hST : (S : Subgroup _).map ((localCentralizer T V E).map
      (QuotientGroup.mk' (Replacement.Transvections.localCore T V E))).subtype ≤
        ((lineT T E).subgroupOf (temporaryLineNormalizer T V E)).map
          (QuotientGroup.mk' (Replacement.Transvections.localCore T V E)))
    (hordinary : ∀ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (localCentralizer T V E),
      A.map (QuotientGroup.mk' (Replacement.Transvections.localCore T V E)) ≠ ⊥ →
        IsOffender σ (A.map (QuotientGroup.mk' (Replacement.Transvections.localCore T V E))))
    (hcore : let δ := imageRepresentation (σ.comp (thompsonImage T V E).subtype)
      ¬ IsStrongFFModule (δ.comp (offenderSubgroup δ).subtype)) :
    offenderSubgroup (σ.comp (thompsonImage T V E).subtype) = ⊤ := by
  obtain ⟨_, _, hodd⟩ := temporary_compatible_sylow_and_odd_kernel Y T V E d σ hker S hST
  exact temporary_generated_of_actionImage_core_bound T V E σ hodd hordinary hcore

omit [Finite G] in
/-- One actual ordinary maximum image makes the core being classified
nontrivial, after restriction to the same I and its faithful action image. -/
theorem thompson_actionImage_offenderCore_ne_bot
    (C : Subgroup G) (q : G →* H) (σ : Representation (ZMod 2) H W)
    (hodd : Odd (Nat.card (actionHom
      (σ.comp ((Stellmacher.elementaryAbelianMaxJ C).map q).subtype)).ker))
    (A : Subgroup G) (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups C)
    (hordinary : IsOffender σ (A.map q)) :
    offenderSubgroup (imageRepresentation
      (σ.comp ((Stellmacher.elementaryAbelianMaxJ C).map q).subtype)) ≠ ⊥ := by
  let I := (Stellmacher.elementaryAbelianMaxJ C).map q
  let ρ := σ.comp I.subtype
  have hAI : A.map q ≤ I := map_mono (le_sSup hA)
  have ho := (hordinary.subgroupOf σ hAI).actionImage_of_odd_kernel ρ hodd
  exact offenderSubgroup_ne_bot_of_ff (imageRepresentation ρ) ⟨_, ho⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer
