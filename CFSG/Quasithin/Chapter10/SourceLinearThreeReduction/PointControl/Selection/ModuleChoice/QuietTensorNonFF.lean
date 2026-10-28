module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorHyperplanes
public import Theory.Representation.BinaryTensorThree.SylowNonFF

/-!
# Non-FF and fusion on the original quiet tensor module

Coordinates on the original Sylow automizer identify its action with a
subaction of the concrete binary tensor Sylow model. The model has no
FF-offenders. Sylow conjugacy therefore rules out offenders in the entire
ambient automizer, and in particular in the literal local L₀T automizer.
Faithfulness of the automizer proves injectivity of the coordinate map.

This discharges the non-FF premise in the quiet core-fusion and original
S = O₂(XT) weak-closure consumers. The actual tensor coordinates, the
point-core inclusion 8.3.12 and the strict bound r > 3 from 8.3.11 remain
source obligations. Neither tensor exclusion nor FixedSupportRowsAt is
asserted here; their assembly remains with the selected-module owner.

Source: Aschbacher--Smith 3.2.10(6b), 8.3.13--14 and H.4.10--11,
printed pp.583--584,727,384.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- Coordinates on the actual Sylow automizer suffice to exclude offenders in the full ambient automizer. -/
theorem quiet_automizer_notFF_of_tensor_sylow
    (q : inducedAutomizer D.fullModule (T : Subgroup G) →* BinaryTensorThree.Small.P)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (he : ∀ (a : inducedAutomizer D.fullModule (T : Subgroup G)) v,
      e (automizerRepresentation D.fullModule a.val v) =
        BinaryTensorThree.Small.actionSmall (q a) (e v)) :
    ¬ IsFFModule (automizerRepresentation D.fullModule) := by
  have hq : Function.Injective q := by
    intro a b hab
    apply Subtype.ext
    apply automizerRepresentation_injective D.fullModule
    apply LinearMap.ext
    intro v
    apply e.injective
    rw [he,he,hab]
  let V := D.fullModule
  let N := normalizer (V : Set G)
  let A := inducedAutomizer V (T : Subgroup G)
  let ρ := automizerRepresentation V
  have hTN : (T : Subgroup G) ≤ N :=
    (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  let S := (T.subtype hTN).mapSurjective
    (MonoidHom.rangeRestrict_surjective V.normalizerMonoidHom)
  have hSA : (S : Subgroup (Automizer V)) ≤ A.subtype.range := by
    rw [range_subtype]
    exact le_rfl
  rintro ⟨B,hB⟩
  obtain ⟨C,hC,hr,hc⟩ := elementary_geometry_of_sylow_range (ρ.comp A.subtype) ρ
    A.subtype A.subtype_injective (LinearEquiv.refl (ZMod 2) (Additive V))
    (fun _ _ => rfl) S hSA B hB.1
  have hCoff : IsOffender (ρ.comp A.subtype) C :=
    ⟨hC,by rw [hc,hr]; exact hB.2⟩
  exact BinaryTensorThree.Small.notFF
    (IsFFModule.map_equivariant (ρ.comp A.subtype) BinaryTensorThree.Small.actionSmall
      q hq e he ⟨C,hCoff⟩)

/-- In particular the literal local L₀T automizer is non-FF, as required by source 3.2.10(6b). -/
theorem quiet_localJoin_notFF_of_tensor_sylow
    (q : inducedAutomizer D.fullModule (T : Subgroup G) →* BinaryTensorThree.Small.P)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (he : ∀ (a : inducedAutomizer D.fullModule (T : Subgroup G)) v,
      e (automizerRepresentation D.fullModule a.val v) =
        BinaryTensorThree.Small.actionSmall (q a) (e v)) :
    ¬ IsFFModule ((automizerRepresentation D.fullModule).comp
      (inducedAutomizer D.fullModule (localJoin T L)).subtype) := by
  intro h
  exact quiet_automizer_notFF_of_tensor_sylow D q e he
    (h.map_equivariant _ _ _ (Subgroup.subtype_injective _)
      (LinearEquiv.refl (ZMod 2) (Additive D.fullModule)) (fun _ _ => rfl))

/-- The quiet tensor fusion consumer, with its non-FF premise discharged by coordinates on the original Sylow automizer. -/
theorem quiet_tensor_intersection_fusion_of_sylow_coordinates
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (q : inducedAutomizer D.fullModule (T : Subgroup G) →* BinaryTensorThree.Small.P)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (he : ∀ (a : inducedAutomizer D.fullModule (T : Subgroup G)) v,
      e (automizerRepresentation D.fullModule a.val v) =
        BinaryTensorThree.Small.actionSmall (q a) (e v))
    {z : G} (hz : orderOf z = 2) (hzV : z ∈ D.fullModule)
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (g x : G) (hxV : x ∈ D.fullModule)
    (hxg : x ∈ D.fullModule.map (MulAut.conj g).toMonoidHom) (hxz : IsConj x z) :
    D.fullModule.map (MulAut.conj g).toMonoidHom ≤ centralizer (D.fullModule : Set G) :=
  quiet_tensor_intersection_fusion D hJ
    (quiet_localJoin_notFF_of_tensor_sylow D q e he) hz hzV hcore g x hxV hxg hxz

/-- The literal S = O₂(XT) consumer with both non-FF and hyperplane geometry supplied by model calculations.
The Sylow augmentation coordinates and the marked radical coordinates may differ;
both identify the same original module and retain the original point. -/
theorem quiet_original_tensor_weakClosure_two_of_sylow_and_radical_coordinates
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (qT : inducedAutomizer D.fullModule (T : Subgroup G) →* BinaryTensorThree.Small.P)
    (eT : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (heT : ∀ (a : inducedAutomizer D.fullModule (T : Subgroup G)) v,
      eT (automizerRepresentation D.fullModule a.val v) =
        BinaryTensorThree.Small.actionSmall (qT a) (eT v))
    {z : G} (hzV : z ∈ D.fullModule)
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule) :
    let S := CentralizerSetup.S ⟨T,localOrbit T L,z⟩
    let hSN : S ≤ normalizer (D.fullModule : Set G) :=
      (CentralizerSetup.S_le_T ⟨T,localOrbit T L,z⟩).trans
        ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
    ∀ (q : S →* BinaryTensorThree.Radical × BinaryTensorThree.Radical)
      (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space),
      (∀ (s : S) (v : Additive D.fullModule),
        e (Additive.ofMul
          (D.fullModule.normalizerMonoidHom ⟨s,hSN s.property⟩ v.toMul)) =
          BinaryTensorThree.action (BinaryTensorThree.radicalPair (q s)) (e v)) →
      e (Additive.ofMul ⟨z,hzV⟩) = BinaryTensorThree.point →
      indexedWeakClosure D.fullModule S 2 ≤ centralizer (D.fullModule : Set G) :=
  quiet_original_tensor_weakClosure_two_of_coordinates D hJ
    (quiet_localJoin_notFF_of_tensor_sylow D qT eT heT) hzV hcore hr

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
