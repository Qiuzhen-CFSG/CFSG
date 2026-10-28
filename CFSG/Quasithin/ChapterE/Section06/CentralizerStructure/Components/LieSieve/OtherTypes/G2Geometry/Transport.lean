module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.G2.Geometry.Generation

/-!
# The G₂ parabolics in the actual component quotient

Map the embedded model parabolics into (L N_Q(L))/O₂(L N_Q(L)).
Their full preimages are the original parabolics joined with the actual
extension core. Thus adjoining Q recovers the original local joins whenever
the extension core lies in Q. Normalizer invariance and generation pass
through these specific quotient maps. No quotient is replaced by a model tag,
and no part of a central-cover kernel is discarded.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the invariant
parabolic argument of E.6.8, printed pp.247–248 (PDF pp.258–259).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.G2Geometry
open Chapter2.ComponentRefinement.LieType.G2
variable {G : Type*} [Group G] {Q L A B : Subgroup G}

/-- Image of the embedded parabolic in the specified component extension quotient. -/
def quotientParabolic (Q L A : Subgroup G) : Subgroup (ComponentQuotient Q L) :=
  (A.subgroupOf (componentExtension Q L)).map (quotientMap Q L)

theorem quotientParabolic_le (hA : A ≤ L) :
    quotientParabolic Q L A ≤ componentImage Q L := map_mono (subgroupOf_mono _ hA)

/-- The full preimage adds precisely the actual extension core. -/
theorem quotientParabolic_preimage (hA : A ≤ L) :
    quotientPreimage Q L (quotientParabolic Q L A) =
      A ⊔ (componentExtension Q L).pCoreIn 2 := by
  rw [quotientPreimage, quotientParabolic, comap_map_eq, Subgroup.map_sup,
    map_subgroupOf_eq_of_le (hA.trans (show L ≤ componentExtension Q L from le_sup_left))]
  rw [quotientMap, QuotientGroup.ker_mk']
  rfl

/-- Joining Q retains the entire preimage kernel, since that kernel lies in Q. -/
theorem quotientParabolic_lift_join (hA : A ≤ L)
    (hcore : (componentExtension Q L).pCoreIn 2 ≤ Q) :
    quotientPreimage Q L (quotientParabolic Q L A) ⊔ Q = A ⊔ Q := by
  rw [quotientParabolic_preimage hA, sup_assoc, sup_eq_right.mpr hcore]

theorem quotientParabolic_invariant (hA : A ≤ L)
    (hN : componentNormalizer Q L ≤ normalizer (A : Set G)) :
    sylowImage Q L ≤ normalizer (quotientParabolic Q L A : Set (ComponentQuotient Q L)) := by
  have hn : (componentNormalizer Q L).subgroupOf (componentExtension Q L) ≤
      normalizer (A.subgroupOf (componentExtension Q L) : Set (componentExtension Q L)) := by
    rw [← subgroupOf_normalizer_eq (hA.trans (show L ≤ componentExtension Q L from le_sup_left))]
    exact subgroupOf_mono _ hN
  exact (map_mono hn).trans ((A.subgroupOf (componentExtension Q L)).le_normalizer_map _)

theorem quotientParabolic_sup (hA : A ≤ L) (hB : B ≤ L) :
    quotientParabolic Q L (A ⊔ B) = quotientParabolic Q L A ⊔ quotientParabolic Q L B := by
  rw [quotientParabolic, subgroupOf_sup (hA.trans (show L ≤ componentExtension Q L from le_sup_left)) (hB.trans (show L ≤ componentExtension Q L from le_sup_left)),
    Subgroup.map_sup]
  rfl

/-- The two model parabolics generate the literal component image. -/
theorem quotientParabolic_pair_generate (d : ParabolicCoordinates L Q) :
    quotientParabolic Q L d.first ⊔ quotientParabolic Q L d.second = componentImage Q L := by
  rw [← quotientParabolic_sup (Q := Q) (show d.first ≤ L from map_subtype_le _)
    (show d.second ≤ L from map_subtype_le _), d.first_sup_second]
  rfl

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.G2Geometry
