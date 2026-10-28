module

public import CFSG.Quasithin.Chapter3.Section02.SourceQrcInput
public import CFSG.Quasithin.Chapter3.Section01.Source318Guarded

/-!
# The FSU qrc configuration under the source standing guard

The Fundamental Setup supplies the local module and all of the hypotheses of
3.1.5 once an `HStar` member is chosen.  The post-2.1.1 source standing guard
supplies such a member by finite minimal descent.  This is the actual Chapter
3 consumer of `StandingGuard`; it does not turn the earlier 3.1.8 ratio claim
into an unconditional theorem.
-/

public section
open Subgroup Theory.GroupTheory
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02
open ChapterD.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  (T : Sylow 2 G) (X M : Subgroup G) (hXM : X ≤ M)
  (hTM : (T : Subgroup G) ≤ M) [(X.subgroupOf M).Normal]
  (hG : IsSimpleQTKE K G) (hM : IsMaximalTwoLocal M)
  (hX : pResidual 2 (X.subgroupOf M) = ⊤)
  (hc : InternalActorCases (T.subtype hTM) (X.subgroupOf M)
    le_normalizer_of_normal)
  (I : Submodule (ZMod 2) (Additive (ReducedNormal.ModuleGroup
    (X ⊔ (T : Subgroup G)))))
  (hI : IsIrrPlus (ReducedNormal.representation (X ⊔ (T : Subgroup G)))
    (X.subgroupOf (X ⊔ (T : Subgroup G))) I)

include hXM hTM hG hM hX hc hI

/-- The source standing guard and the FSU local hypotheses produce an actual
`HStar` qrc configuration. -/
theorem source_reduced_seed_qrc_configuration_of_standing_guard
    (houtside : Chapter3.HasMaximalOutside T M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      X ⊔ (T : Subgroup G) ≤ N → N = M) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) M ∧
      ChapterD.QRCConfiguration (X ⊔ (T : Subgroup G)) H
        (T : Subgroup G) (componentOrbit
          (ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I)
          (T : Subgroup G)) := by
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside houtside
  refine ⟨H, hH, ?_⟩
  exact source_reduced_seed_qrc_configuration T X M hXM hTM hG hM hX hc I hI hu hH

/-- The same actual consumer can retain the guarded earlier ratio input beside
the qrc configuration.  This is the source-correct Chapter 3 interface: the
standing guard supplies `HStar`, while the earlier ratio implication remains
an explicit conditional input. -/
theorem source_reduced_seed_qrc_and_guarded_ratio
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (houtside : Chapter3.HasMaximalOutside T M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      X ⊔ (T : Subgroup G) ≤ N → N = M) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) M ∧
      ChapterD.QRCConfiguration (X ⊔ (T : Subgroup G)) H
        (T : Subgroup G) (componentOrbit
          (ReducedNormal.subspaceImage (X ⊔ (T : Subgroup G)) I)
          (T : Subgroup G)) ∧
      Chapter3.SourceTheorem318OneAt T M := by
  obtain ⟨H, hH, hqrc⟩ :=
    source_reduced_seed_qrc_configuration_of_standing_guard T X M hXM hTM hG hM hX hc I hI
      houtside hu
  refine ⟨H, hH, hqrc, ?_⟩
  exact Chapter3.sourceTheorem318OneAt_of_guarded h318 hM hTM houtside

end CFSG.Quasithin.Chapter3.Section02
