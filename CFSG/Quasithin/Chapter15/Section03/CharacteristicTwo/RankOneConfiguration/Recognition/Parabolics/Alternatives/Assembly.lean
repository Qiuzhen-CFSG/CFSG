module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.Seven
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.LieSieve
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.EightFlags

/-!
# Exhaustive marked alternatives in 15.3.28

Apply the universal earlier FF component list to the actual Thompson
action after checking B.5.3. The partition-stabilizer argument excludes
A₇; the complete Lie-model inspection supplies a marked even-degree
PSL₂ Borel, a small derived-group parabolic with trivial diagram action,
or the intrinsic outer middle node. In the last case, the compatible
exceptional comparison constructs an actual S₈ action with the even
component intersection, full extended intersection and common Sylow flag.

Relative component normality, Y₊ containment and the displayed earlier
local facts remain explicit inputs, as does the universal earlier-source
component theorem for K. No local model, parabolicity, recognition or
later branch exclusion is assumed. The parent source assembly supplies
these earlier inputs and retains the proof of 15.3.25.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.3–6,
printed pp.104–105 (PDF pp.115–116), and 15.3.26–28,
printed pp.1130–1131 (PDF pp.1147–1148).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}

/-- The exhaustive marked alternatives, with every local classification and
geometric input constructed from the earlier source contract. -/
theorem markedAlternative_of_source {K : GroupClass.{u}}
    (source : ComponentClassificationInput K) (hSQTK : IsSQTK K I)
    (a : LieSieve.Input d I c) : MarkedAlternative d I c := by
  have hmodel := component_model_of_source source d c hSQTK a.characteristicTwo
    a.module_le a.sylow a.sylow_eq a.normal
  have hA7 := component_star_not_alternating_seven d c a.minimal a.facts a.rank
    a.normal a.sylow a.sylow_eq
  cases LieSieve.lieParabolicAlternative a hmodel hA7 with
  | linearTwo F marking => exact .linearTwo F marking
  | small marking => exact .small marking
  | middle marking =>
    obtain ⟨flag⟩ := middleNodeFlagMarking_of_outerMiddleNodeData d c a.normal
      a.generated a.sylow a.sylow_eq a.kernel_le marking
    exact .middle flag

/-- Source 15.3.28 under the inherited earlier-source contract, exposing all
local premises separately. The three outputs retain their actual model
isomorphisms, subgroup markings and diagram or simultaneous flag actions. -/
theorem lemma_15_3_28_of_source {K : GroupClass.{u}}
    (source : ComponentClassificationInput K)
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hSQTK : IsSQTK K I) (hI : I ∈ d.HplusMinimal)
    (hf : HasCharacteristicTwo I) (hr : primeRank 3 d.Yplus = 1)
    (hcontrol : SolvableInvariantControl d I) (hfacts : RankOneFacts d I)
    (hn : (c.L.subgroupOf I).Normal) (hYL : d.Yplus ≤ c.L)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hVT : d.V ≤ (d.T : Subgroup G))
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I) :
    MarkedAlternative d I c :=
  markedAlternative_of_source source hSQTK
    { minimal := hI
      characteristicTwo := hf
      rank := hr
      facts := hfacts
      solvableControl := hcontrol
      normal := hn
      contains := hYL
      sylow := P
      sylow_eq := hP
      module_le := hVT
      kernel_le := hc }

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
