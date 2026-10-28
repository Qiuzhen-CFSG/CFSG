module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.NaturalCoreModels.SourceWitnesses
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.LinearThree
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.ContainedCoreModels.G2Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedModelAssembly.Linear
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedModelAssembly.Alternating
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedModelAssembly.G2

/-!
# All marked small-core exclusions and the original linear source branch

The two natural-core proofs complete the five marked alternatives: the existing
block and nonabelian-core calculations handle the other three. Applying this
exhaustion to the actual marked-model construction excludes every surviving
C.1.34 case, using only the genuine source setup, MS output and small parabolic
marking. No additional core-centralization or model certificate is retained.

Source: Aschbacher–Smith, proof of 15.3.31, printed p.1132 (PDF p.1149).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.NaturalCoreModels.SourceWitnesses
open CentralCover CentralCover.LinearModels LinearThree
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
  {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

/-- All five genuinely marked source models are excluded, without a core premise. -/
theorem excluded_of_marked_models (s : SourceData κ d c)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (m : MarkedModels c.L d.V₂ (d.M ⊓ c.L)) : False := by
  let := ms.simple
  cases m with
  | alternating hs model plane dimension invariant parabolic =>
    exact ContainedCoreModels.alternating_excluded
      s hs model plane dimension invariant parabolic
  | g2 hs model parabolic =>
    exact ContainedCoreModels.g2_excluded s hs model parabolic
  | linearOne core plane => exact excluded_one s core plane
  | linearTwo core plane => exact excluded_two s core plane
  | linearThree center plane dual =>
    exact ContainedCoreModels.linearThree_excluded s center plane dual

/-- The complete C.1.34 source branch, with its actual marked models constructed. -/
theorem excluded_of_linear_survivors (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (e : (c.L ⧸ pCore 2 c.L) ≃* SL)
    (h : MarkedMS.LinearThreeSurvivors c.L d.S e) : False :=
  excluded_of_marked_models s ms (MarkedModelAssembly.linear_marked_models s hm ms e h)

/-- The complete small alternative of 15.3.31, retaining only genuine earlier inputs. -/
theorem excluded_of_source (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq) : False := by
  rcases ms.cases with ⟨hb, ha⟩ | ⟨hb, hg⟩ | ⟨e, h⟩
  · exact excluded_of_marked_models s ms
      (MarkedModelAssembly.alternating_marked_models s hm ms hb ha)
  · exact excluded_of_marked_models s ms
      (MarkedModelAssembly.g2_marked_models s hm ms hb hg)
  · exact excluded_of_linear_survivors s hm ms e h

/-- The original small-source exclusion after applying the genuine earlier classifications. -/
theorem excluded_of_classifications (s : SourceData κ d c)
    (earlier : MarkedMS.EarlierMSClassifications κ)
    (ff : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.CompleteClassificationInput.{u,u} κ)
    (hm : Parabolics.SmallParabolicMarking d I c.L) : False :=
  excluded_of_source s hm (s.markedMS earlier ff hm)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.NaturalCoreModels.SourceWitnesses
