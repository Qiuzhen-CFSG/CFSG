module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.Marking
public import Theory.Representation.FirstCohomologyG2Natural.BinaryGeneration

/-!
# Marked coefficient models for the A₆ and G₂(2)' block alternatives

The input is the genuine short-block conclusion and an equivariant natural
module identification of the actual quotient U(L)/C_U(L)(L). We construct
the literal Z(Q)/C_Z(Q)(L) model with the same L/O₂(L) quotient map. The
source parabolic stabilizes the marked V₂-plane, and its O^{3′} residual
contains concrete cubic elements that detect every coefficient cocycle.
Thus the output is directly usable by `centralizerImage_eq_bot_of_detected_model`.
No centralizer D or conclusion about D is part of these model theorems.

For A₆ the checked natural flag geometry identifies any T₀-invariant plane.
For G₂ the input natural-module coordinates retain the marked null plane.
The checked generating-pair theorem for the actual derived octonion group
discharges the premise of `FirstCohomologyG2Natural.BinaryBound`. Thus
`g2_model_and_marking` has no generation or cohomology hypothesis; the
earlier conditional adapter is retained as a separate public interface.

The earlier MS classification, actual natural-module equivalences, and the
source parabolic/residual identifications are conditional inputs, as required
by this task's contract. The parent retains their source assembly and D⁺ = 1.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), C.1.7,
C.1.12--13, C.1.31--34, I.1.5--6, I.2.3 and 15.3.31, printed p.1132.
The proof uses direct cocycles, so no unproved self-duality identification
or application of a cover theorem in the wrong dual orientation is needed.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.BlockModels

variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {L : Subgroup G}

/-- The full coefficient marking is the original block marking, including
its central kernel; this complements `centerModel_actorMap`. -/
theorem centerModel_coordinates (h : ChapterC.IsShort L)
    (ρ : Representation (ZMod 2) A V)
    (m : ChapterC.BlockModuleModel L (multiplicativeAction ρ)) (u : ChapterC.blockU L) :
    (centerModel h ρ m).coordinates (blockCenterEquiv h u) =
      m.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L) u) := by
  change m.moduleIso ((blockCenterQuotientEquiv h).symm
    (QuotientGroup.mk' (centerKernel L) (blockCenterEquiv h u))) = _
  rw [← blockCenterQuotientEquiv_mk, MulEquiv.symm_apply_apply]

/-- A₆-block model and marked cocycle detection. The plane is the actual
coefficient image of V₂, with the source Sylow action in the same coordinates.
The parabolic and O^{3′} identities are the genuine earlier source conclusions. -/
theorem alternating_model_and_marking [Finite G]
    (h : ChapterC.IsShort L)
    (m : ChapterC.BlockModuleModel L (multiplicativeAction Alternating.action))
    (P : Subgroup L) (Yplus : Subgroup G)
    (hY : Yplus.subgroupOf L = (primeToResidual 3 P).map P.subtype)
    (W : Submodule (ZMod 2) Alternating.Coefficients)
    (hdim : Module.finrank (ZMod 2) W = 2)
    (hW : ∀ g ∈ Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.T0,
      W.map (BinaryPermutation.naturalRepresentation (Fin 6) g) = W)
    (hP : P.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
      planeStabilizer Alternating.action W) :
    ∃ c : CenterModel L Alternating.action,
      c.quotientIso = m.quotientIso ∧
      c.actorMap = m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)) ∧
      (∀ u : ChapterC.blockU L, c.coordinates (blockCenterEquiv h u) =
        m.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L) u)) ∧
      Function.Injective Alternating.action ∧
      DetectedOn Alternating.action ((Yplus.subgroupOf L).map c.actorMap) := by
  let c := centerModel h Alternating.action m
  refine ⟨c, rfl, rfl, centerModel_coordinates h _ m, Alternating.faithful, ?_⟩
  have hp : P.map c.actorMap = planeStabilizer Alternating.action W := hP
  rw [marking_image c P (Yplus.subgroupOf L) hY, hp]
  exact Alternating.detectedOn_invariantPlane_residual W hdim hW

/-- G₂(2)'-block model and marked cocycle detection, retaining the actual
derived actor and the same marked null plane in the coefficient equivalence.
This conditional interface exposes the generation step; `g2_model_and_marking`
below discharges it using the checked concrete generating-pair theorem. -/
theorem g2_model_and_marking_of_generation [Finite G]
    (h : ChapterC.IsShort L)
    (m : ChapterC.BlockModuleModel L (multiplicativeAction G2.action))
    (P : Subgroup L) (Yplus : Subgroup G)
    (hY : Yplus.subgroupOf L = (primeToResidual 3 P).map P.subtype)
    (hP : P.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
      planeStabilizer G2.action G2.markedPlane)
    (hgen : closure ({Atlas.G2.Natural.binaryA (ZMod 2), Atlas.G2.Natural.binaryB (ZMod 2)} :
      Set G2.Actor) = ⊤) :
    ∃ c : CenterModel L G2.action,
      c.quotientIso = m.quotientIso ∧
      c.actorMap = m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)) ∧
      (∀ u : ChapterC.blockU L, c.coordinates (blockCenterEquiv h u) =
        m.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L) u)) ∧
      Function.Injective G2.action ∧
      DetectedOn G2.action ((Yplus.subgroupOf L).map c.actorMap) := by
  let c := centerModel h G2.action m
  refine ⟨c, rfl, rfl, centerModel_coordinates h _ m, G2.faithful, ?_⟩
  have hp : P.map c.actorMap = planeStabilizer G2.action G2.markedPlane := hP
  rw [marking_image c P (Yplus.subgroupOf L) hY, hp]
  exact G2.detectedOn_markedPlane_residual hgen

/-- G₂(2)'-block model and marked detection of every cocycle, including
principal cocycles. The only inputs are the earlier short-block conclusion,
the actual natural-module equivalence with its marked V₂-plane, and the
source parabolic and O^{3′} residual identities. The original quotient and
coefficient markings are preserved for the star-map comparison. -/
theorem g2_model_and_marking [Finite G]
    (h : ChapterC.IsShort L)
    (m : ChapterC.BlockModuleModel L (multiplicativeAction G2.action))
    (P : Subgroup L) (Yplus : Subgroup G)
    (hY : Yplus.subgroupOf L = (primeToResidual 3 P).map P.subtype)
    (hP : P.map (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) =
      planeStabilizer G2.action G2.markedPlane) :
    ∃ c : CenterModel L G2.action,
      c.quotientIso = m.quotientIso ∧
      c.actorMap = m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)) ∧
      (∀ u : ChapterC.blockU L, c.coordinates (blockCenterEquiv h u) =
        m.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L) u)) ∧
      Function.Injective G2.action ∧
      DetectedOn G2.action ((Yplus.subgroupOf L).map c.actorMap) :=
  g2_model_and_marking_of_generation h m P Yplus hY hP
    (Atlas.G2.Natural.binary_pair_generates (ZMod 2) (by simp))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.BlockModels
