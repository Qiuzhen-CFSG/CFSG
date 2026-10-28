module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Linear
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Symplectic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.G2
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Triality
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores.Ree

/-!
# Self-centralizing two-cores in rank-two parabolics

For PSL₃, PSp₄, G₂, genuine triality and Ree, the concrete geometry places
every proper Borel overgroup in a full parabolic with self-centralizing
two-core. Sylow-overgroup inheritance includes the Borel itself. Actual
model isomorphisms and Sylow conjugacy transport these calculations, and
restriction to the literal component image gives `rankTwo_parabolicCores`.
The field-degree hypothesis excludes the degree-one derived and Tits cases;
the Ree branch retains its odd-degree and nonbinary restrictions.

Source: Aschbacher--Smith, 15.3.43, printed p.1140, with the model list
from 1.1.5(3)(a)--(c), pp.501--502, and A.2.4, p.33.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- The triality branch uses the actual quotient model and specified Sylow. -/
theorem triality_parabolicCores
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {n : ℕ}
    (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) (c.toComponentAction.image L)) :
    ParabolicCores (c.toComponentAction.image L) (c.toComponentAction.image S) := by
  obtain ⟨T, hT⟩ := quotient_component_sylow c
  exact parabolicCores_of_borelOvergroupCores _ _ T hT (triality_borelOvergroupCores hm)

/-- The Ree branch retains its nonbinary parameter restriction. -/
theorem ree_parabolicCores
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {m : ℕ} (hm : 1 ≤ m)
    (he : Nonempty (c.toComponentAction.image L ≃* ReeF4.Model m)) :
    ParabolicCores (c.toComponentAction.image L) (c.toComponentAction.image S) := by
  obtain ⟨e⟩ := he
  obtain ⟨T, hT⟩ := quotient_component_sylow c
  exact parabolicCores_of_borelOvergroupCores _ _ T hT
    (borelOvergroupCores_of_mulEquiv e (ree_borelOvergroupCores m hm))

/-- Exhaustive assembly with the three split-family calculations explicit.
`rankTwo_parabolicCores` below supplies these calculations from the models. -/
theorem rankTwo_parabolicCores_of_split_models
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {n : ℕ} (hn : 1 < n)
    (hm : ChapterA.Section02.IsTheoremCRankTwoModel (c.toComponentAction.image L) n)
    (hlinear : ClassicalGroup.IsPSL (c.toComponentAction.image L) 3 (2 ^ n) →
      BorelOvergroupCores (c.toComponentAction.image L))
    (hsymplectic : ClassicalGroup.IsPSp (c.toComponentAction.image L) 2 (2 ^ n) →
      BorelOvergroupCores (c.toComponentAction.image L))
    (hg2 : ClassificationModels.IsG2At (c.toComponentAction.image L) (2 ^ n) →
      BorelOvergroupCores (c.toComponentAction.image L)) :
    ParabolicCores (c.toComponentAction.image L) (c.toComponentAction.image S) := by
  obtain ⟨T, hT⟩ := quotient_component_sylow c
  apply parabolicCores_of_borelOvergroupCores _ _ T hT
  cases hm with
  | linear _ hi => exact hlinear hi
  | symplectic _ hi => exact hsymplectic hi
  | g2 _ hi => exact hg2 hi
  | triality _ hi => exact triality_borelOvergroupCores hi
  | ree_f4 m hm _ hi =>
    obtain ⟨e⟩ := hi
    exact borelOvergroupCores_of_mulEquiv e (ree_borelOvergroupCores m hm)
  | symplectic_derived he _ => omega
  | g2_derived he _ => omega
  | tits he _ => omega

/-- Every proper Borel overgroup in the rank-two component image has a
self-centralizing intrinsic two-core. All model calculations and parabolic
coverage are discharged, including the case of the Borel itself. -/
theorem rankTwo_parabolicCores
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {n : ℕ} (hn : 1 < n)
    (hm : ChapterA.Section02.IsTheoremCRankTwoModel (c.toComponentAction.image L) n) :
    ParabolicCores (c.toComponentAction.image L) (c.toComponentAction.image S) := by
  exact rankTwo_parabolicCores_of_split_models c hn hm
    (linearThree_borelOvergroupCores hn)
    (symplecticFour_borelOvergroupCores hn)
    g2_borelOvergroupCores

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
