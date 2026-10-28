module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ModelTransport

/-!
# Common marked models for both extension branches

These output alternatives use the actual Q = [O₂(L),L], Z(Q), and quotient
actor. In the third linear case both dual summands are identified using
the very same actor as Z(Q). Thus the central and noncentral calculations
can share their marking without losing a module layer.

The forgetful map feeds the already checked central-cover calculation.
Existence of these marked models and the remaining noncentral calculations
are not asserted here. Final source assembly must prove both.

Source: Aschbacher–Smith, proof of 15.3.31, printed p.1132 (PDF p.1149).
-/

@[expose] public section

open Subgroup Representation
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover
variable {G : Type*} [Group G]

/-- Output of the MS-to-model comparison, retaining the common dual actor
in C.1.34(3). Existence is a separate mathematical obligation. -/
inductive MarkedModels (L E P : Subgroup G) : Prop
  | alternating
      (short : ChapterC.IsShort L)
      (model : ChapterC.BlockModuleModel L
        (BlockModels.multiplicativeAction BlockModels.Alternating.action))
      (plane : Submodule (ZMod 2) BlockModels.Alternating.Coefficients)
      (dimension : Module.finrank (ZMod 2) plane = 2)
      (invariant : ∀ g ∈ Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.T0,
        plane.map (BinaryPermutation.naturalRepresentation (Fin 6) g) = plane)
      (parabolic : (P.subgroupOf L).map
        (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
          BlockModels.planeStabilizer BlockModels.Alternating.action plane)
  | g2
      (short : ChapterC.IsShort L)
      (model : ChapterC.BlockModuleModel L
        (BlockModels.multiplicativeAction BlockModels.G2.action))
      (parabolic : (P.subgroupOf L).map
        (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
          BlockModels.planeStabilizer BlockModels.G2.action BlockModels.G2.markedPlane)
  | linearOne
      (core : LinearModels.AbelianCore L LinearThree.natural)
      (plane : LinearModels.MarkedPlane core.fullCenter E)
  | linearTwo
      (core : LinearModels.AbelianCore L (LinearThree.natural.prod LinearThree.natural))
      (plane : LinearModels.MarkedPlane core.fullCenter E)
  | linearThree
      (center : LinearModels.FullCenter L LinearThree.natural)
      (plane : LinearModels.MarkedPlane center E)
      (dual : CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.HasSectionModel
        L (extensionCore L) (coreCenter L) center.actor
        (LinearThree.natural.dual.prod LinearThree.natural.dual))

theorem MarkedModels.toCentralCover {L E P : Subgroup G} (m : MarkedModels L E P) :
    MarkedConfiguration L E P := by
  cases m with
  | alternating hs m W hd hW hP => exact .alternating hs m W hd hW hP
  | g2 hs m hP => exact .g2 hs m hP
  | linearOne c p => exact .linearOne c p
  | linearTwo c p => exact .linearTwo c p
  | linearThree c p _ => exact .linearThree c p

variable [Finite G]

/-- The actual centralizer equality, once the two outstanding model obligations
have supplied marked coordinates and core centralization. -/
theorem SourceData.centralizers_eq_of_models {κ : GroupClass} {d : LocalData G}
    {I : Subgroup G} {c : ComponentWitness d I} (s : SourceData κ d c)
    (m : MarkedModels c.L d.V₂ (d.M ⊓ c.L))
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) :
    I ⊓ centralizer (d.Yplus : Set G) = I ⊓ centralizer (c.L : Set G) :=
  centralizers_eq_of_marked_configuration d c s.contains s.normal s.component_parabolic
    s.component_residual m.toCentralCover hDQ

/-- Apply that equality to the original V₁, with its earlier source normalizer
bound discharged by SourceData. The marked models and core centralization
remain explicit; this is not the completed exclusion of 15.3.28(2). -/
theorem SourceData.excluded_of_models {κ : GroupClass} {d : LocalData G}
    {I : Subgroup G} {c : ComponentWitness d I} (s : SourceData κ d c)
    (m : MarkedModels c.L d.V₂ (d.M ⊓ c.L))
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) : False := by
  obtain ⟨hVI, hVY, hN⟩ := s.first_plane_control
  exact excluded_of_equal_centralizers d c hVI hVY hN
    (s.centralizers_eq_of_models m hDQ)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension

end
