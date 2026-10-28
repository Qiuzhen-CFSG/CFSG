module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits.EarlierThirteen
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.FromRechoice

/-!
# The literal rechoice-generation consumer without an earlier-13 premise

Apply the source 14.7.12–13 producer at every allowed rechoice of the one
original critical path. This removes EarlierThirteen from the genuine
14.7.70-to-72 generation application. The independent earlier image,
section, point-commutator and 14.7.68 inputs retain their existing source
producers; the original Data, path, actors and quotient maps are unchanged.

Source: Aschbacher–Smith 14.7.13 and 14.7.70–72, pp.1046,1074–1076.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation.MarkedSpans
open SourceEndgame.SteinbergRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The actual selected-path generation theorem now consumes the proved earlier13 source. -/
theorem generation_of_rechoice (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (c : CriticalPath (L := L) F) (images : c.EarlierImages)
    (sep : d.ModuleSeparation) (hc : d.SectionCentralizer)
    (mark : UpperMarking d) (actors : LocalActors d)
    (h69 : Nat.card (star F c.Uα) = 2) (h70 : Rechoice.Statement c d)
    (hpoint : ∀ n : Rechoice.group F L, F.Vi 1 ≤ ⁅F.U, (c.reselect n).Uα⁆)
    (h68 : ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 →
      d.FixedModuloPoint u → centralizer ({(u : G)} : Set G) ≤ F.H) :
    SourceGeneration.Conclusion d :=
  SourceEndgame.SourceAssembly.generation_of_rechoice d structural c images sep hc mark actors
    h69 h70 (earlier_thirteen_reselect d structural c) hpoint h68

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceOrbits
