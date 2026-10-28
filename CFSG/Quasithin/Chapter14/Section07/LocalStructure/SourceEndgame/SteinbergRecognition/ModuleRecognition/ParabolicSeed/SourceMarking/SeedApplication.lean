module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed.SourceMarking
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed

/-!
# Applying the compatible source marking to the original plane

The source marking constructor discharges the marking premise in the existing
cyclic-seed and H.6.5 applications, with the original quotient and inverse
actor twist. The local transitivity of the original U/V plane and the earlier
module separation and U₀ = V₁ conclusions remain explicit. Their source
producers and the final 14.7.72 assembly are independent of this marking step.

Source: Aschbacher–Smith, proof of 14.7.72, printed p.1076 (PDF p.1093),
and H.6.5, printed p.388 (PDF p.399), manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed
open Chapter12.Section08 CriticalFusion.Source BinaryLinearThree.ParabolicCyclic
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  [(V.subgroupOf (S F L)).Normal]
  [IsElementaryAbelian 2 (S F L ⧸ V.subgroupOf (S F L))]

/-- The original quotient has a compatible marking and a cyclic plane seed;
only the independent source local-action and earlier-module premises remain. -/
theorem exists_source_seed_of_local_transitive
    (hTL : (T : Subgroup G) ≤ normalizer L) (a : QuotientAction d)
    (hs : d.ModuleSeparation) (hU₀ : d.U₀ = F.Vi 1) (hlocal : LocalTransitive d a) :
    ∃ (b : Marking d) (s : S F L), (s : G) ∈ F.U ∧ (s : G) ∉ V ∧
      (∀ g ∈ Matrix.PSL3Two.borelSL, (a.representation.comp b.twist.toMonoidHom) g
        (quotientCoordinates s).toAdd = (quotientCoordinates s).toAdd) ∧
      orbitSpan (a.representation.comp b.twist.toMonoidHom) ⊤
        (quotientCoordinates s).toAdd = ⊤ ∧
      Module.finrank (ZMod 2) (orbitSpan (a.representation.comp b.twist.toMonoidHom)
        Matrix.PSL3Two.lineParabolicSL (quotientCoordinates s).toAdd) = 2 := by
  obtain ⟨b⟩ := nonempty_marking d hTL
  exact ⟨b, exists_seed_of_local_transitive d b a hs hU₀ hlocal⟩

/-- H.6.5 applies with a marking constructed from the source data and the
original Sylow normalization; no compatible-marking witness is assumed. -/
theorem source_alternatives_of_local_transitive
    (hTL : (T : Subgroup G) ≤ normalizer L) (a : QuotientAction d)
    (hs : d.ModuleSeparation) (hU₀ : d.U₀ = F.Vi 1) (hlocal : LocalTransitive d a) :
    ∃ b : Marking d, Alternatives (a.representation.comp b.twist.toMonoidHom) := by
  obtain ⟨b⟩ := nonempty_marking d hTL
  exact ⟨b, alternatives_of_local_transitive d b a hs hU₀ hlocal⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.ModuleRecognition.ParabolicSeed
