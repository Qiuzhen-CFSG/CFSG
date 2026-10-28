module

public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.SourceRecognition
public import Theory.GroupTheory.Recognition.HeldM22A10.Complete
public import Theory.SpecificGroups.Alternating.QuasithinBounds

/-!
# Global identification from the equality-branch centralizer geometry

The marked source centralizer construction gives Held's local recognition
data on the original group and Sylow subgroup. Held's theorem identifies
the ambient simple group with M₂₂ or A₁₀. The latter is impossible: its
disjoint A₄ × A₆ subgroup lies in a two-local and has three-rank three.

This completes the global identification step from the explicit earlier
geometry in the equality branch. Constructing that geometry, proving the
natural reduction, and excluding the strict-intersection branch remain
source obligations; none is asserted by this conditional result.

Source: Aschbacher--Smith, Proposition 6.2.13, printed p.688;
Huppert--Blackburn III, XII.1.18(b), printed p.314.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source equality-branch geometry gives an actual M₂₂ isomorphism.
The A₁₀ alternative is excluded by a proved two-local rank obstruction. -/
theorem m22_of_source_geometry
    {κ : GroupClass.{u}} {T : Sylow 2 G} {L M V₀ : Subgroup G} {n : ℕ}
    (h611 : Hypothesis611 κ T L M V₀ n)
    (h6127 : Conclusion6127 (T : Subgroup G) L M V₀ n)
    (H : Subgroup G) (z : G) (hH : H = centralizer ({z} : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    [((layer L V₀).subgroupOf M).Normal]
    (hq : CompatibleSymmetricFiveQuotient ((layer L V₀).subgroupOf M) (L.subgroupOf M))
    (P : Subgroup H) [P.Normal] (hP : CoreData P)
    (ha : NaturalFourOrbit P ((ZS (T : Subgroup G) L V₀).subgroupOf H))
    (hZS : coreCenter P ≤ (ZS (T : Subgroup G) L V₀).subgroupOf H)
    (hSP : (ZS (T : Subgroup G) L V₀).subgroupOf H ≤ P)
    (hPT : P.map H.subtype ≤ (T : Subgroup G))
    (hbranch : (sourceEight ((ZS (T : Subgroup G) L V₀).subgroupOf H)).map H.subtype ⊓
      layer L V₀ = ZS (T : Subgroup G) L V₀)
    (d : G) (hdL : d ∈ L)
    (hdT : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd : orderOf d = 3) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  let : IsSimpleGroup G := h611.simpleQTKE.simple
  obtain ⟨D⟩ := source_nonempty_recognition_localData h611 h6127 H z hH hTH
    hq P hP ha hZS hSP hPT hbranch d hdL hdT hd
  rcases HeldM22A10.recognition D with hm22 | ha10
  · exact hm22
  · obtain ⟨e⟩ := ha10
    exact (alternatingGroup.not_quasithin_ten
      (isQuasithin_of_equiv e h611.simpleQTKE.quasithin)).elim

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
