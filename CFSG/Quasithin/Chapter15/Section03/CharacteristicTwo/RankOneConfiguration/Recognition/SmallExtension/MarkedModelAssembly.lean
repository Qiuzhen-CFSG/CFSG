module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.Configurations
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedModelAssembly.Linear

/-!
# Assembly of the classified constituents into extension models

The three linear cases have their original V₂-plane inside an actual natural
copy of the whole center. The source reduction below leaves only the A₆ and G₂
blocks, with their full block predicates. Their compatible coefficient and
parabolic markings still have to be constructed; this module does not assert
the completed five-case model theorem.

For the linear branch we apply the constructed coordinates to the actual
centralizer equality and source exclusion. Only centralization of the
commutator core remains explicit in those applications, after selecting the
linear alternative. Final model assembly stays here; final core centralization
and the unrestricted source exclusion belong to the SmallExtension parent.

Source: Aschbacher–Smith, proof of 15.3.31, printed p.1132 (PDF p.1149),
using C.1.7 and C.1.30–34 and B.5.3–6.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

/-- The completed linear construction reduces model assembly to the two genuine
block branches. The block predicates retain their central quotients and actions. -/
theorem SourceData.markedModels_or_block (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq) :
    MarkedModels c.L d.V₂ (d.M ⊓ c.L) ∨
      ((ChapterC.IsBlock (c.L.subgroupOf (c.L ⊔ d.S)) ∧ ChapterC.IsAlternatingBlock c.L 6) ∨
       (ChapterC.IsBlock (c.L.subgroupOf (c.L ⊔ d.S)) ∧ IsG2TwoBlock c.L)) := by
  rcases ms.cases with h | h | ⟨e, h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inl (MarkedModelAssembly.linear_marked_models s hm ms e h)

/-- In the linear branch the source centralizer calculation needs no extra
model-placement input: only the remaining core-centralization argument. -/
theorem SourceData.centralizers_eq_of_linear_survivors (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (e : (c.L ⧸ pCore 2 c.L) ≃* CentralCover.LinearThree.SL)
    (h : MarkedMS.LinearThreeSurvivors c.L d.S e)
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) :
    I ⊓ centralizer (d.Yplus : Set G) = I ⊓ centralizer (c.L : Set G) :=
  s.centralizers_eq_of_models (MarkedModelAssembly.linear_marked_models s hm ms e h) hDQ

/-- Apply the constructed linear models to the original V₁ exclusion. -/
theorem SourceData.excluded_of_linear_survivors (s : SourceData κ d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (ms : MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo
      s.sylow s.sylow_eq)
    (e : (c.L ⧸ pCore 2 c.L) ≃* CentralCover.LinearThree.SL)
    (h : MarkedMS.LinearThreeSurvivors c.L d.S e)
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) : False :=
  s.excluded_of_models (MarkedModelAssembly.linear_marked_models s hm ms e h) hDQ

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension

end
