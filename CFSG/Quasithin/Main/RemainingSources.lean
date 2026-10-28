module

public import CFSG.Quasithin.MainForward.Chapter2Complete
public import CFSG.Quasithin.MainForward.RemainingSources
public import CFSG.Quasithin.Chapter15.SourceAssembly.MSClassifications
public import CFSG.Quasithin.Chapter15.SourceAssembly.SingletonResolvers
public import CFSG.Quasithin.MainConverse

/-!
# The complete classification statement from the remaining source inputs

For finite nonabelian simple groups with the full proper-K induction
hypothesis, the already proved converse gives one direction of the Main
Theorem. The forward direction uses the complete Chapter 2 theorem and the
two original multiple-overgroup branches D and E. The second assembly below
supplies E from the shared small MS classifications and original 15.1.3.
The final assembly accepts the two pointwise 15.1.3 branch resolvers, retaining
the singleton-centralizer hypothesis when applying them.

All missing source inputs remain explicit. These composition theorems are
not an unconditional proof of the Main Theorem. In particular, neither an
MS-classification callback nor the original D and 15.1.3 branches is assumed
as an axiom. The complete output predicate retains the Ree family.

Source: Aschbacher--Smith, Main Theorem 0.1.2, printed p.4, and its proof
on p.1166; the Theorem E reduction on pp.1086 and 1165.
-/

public section

namespace CFSG.Quasithin

open Subgroup Theory.GroupTheory ClassificationModels
open ChapterA.Section05To06 Chapter15.Section03
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

/-- The exact proper-K Main Theorem equivalence after supplying D and E.
The unique-overgroup branch and the whole converse are discharged here. -/
theorem classification_of_theoremsD_and_E
    (hna : ¬ IsMulCommutative G)
    (hK : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hD : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      (MainForward.faithfulLocalComponents T).Nonempty → IsTheoremDModel G)
    (hE : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ → IsTheoremEModel G) :
    (IsQuasithin G ∧ IsEvenCharacteristic G) ↔ IsQTKEModel G := by
  constructor
  · rintro ⟨hQT, hEC⟩
    have hG : IsSimpleQTKE KnownSimple.IsKnownSimple G :=
      ⟨⟨hQT, hK, hEC⟩, inferInstance, hna⟩
    exact MainForward.forward_of_complete_alternating_five_source hG (hD hG) (hE hG)
  · exact MainConverse.quasithin_and_evenCharacteristic_of_model hna

/-- The final equivalence with E reduced to its actual earlier MS input and
original singleton-centralizer branch. Both characteristic-two exclusions
and all subsequent E arguments are supplied by the existing source proof. -/
theorem classification_of_MS_and_remaining_sources
    (earlier : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hna : ¬ IsMulCommutative G)
    (hK : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hD : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      (MainForward.faithfulLocalComponents T).Nonempty → IsTheoremDModel G)
    (h1513 : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ → ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      IsTheoremEModel G ∨ ∃ M : Subgroup G, IsOrderingMaximal T M ∧
        Nonempty (NaturalOrthogonalAction M (localModule T M))) :
    (IsQuasithin G ∧ IsEvenCharacteristic G) ↔ IsQTKEModel G := by
  apply classification_of_theoremsD_and_E hna hK hD
  intro hG T hmany hempty
  exact Chapter15.source_theoremE_of_MS_classifications earlier hG T hmany hempty
    (h1513 hG T hmany hempty)

/-- The Main Theorem consumer of the separately produced MS classifications
and singleton branch resolvers. D remains independent, and the centralizing
continuation may use the rank-two resolver at the same actual Mc. -/
theorem classification_of_MS_and_singleton_resolvers
    (earlier : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple)
    (hna : ¬ IsMulCommutative G)
    (hK : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hD : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      (MainForward.faithfulLocalComponents T).Nonempty → IsTheoremDModel G)
    (hrank : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ → ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
        Chapter15.Section01.RankTwoResolver T Mc)
    (hcentral : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ → ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
        Chapter15.Section01.RankTwoResolver T Mc →
        Chapter15.Section01.CentralizingResolver T Mc) :
    (IsQuasithin G ∧ IsEvenCharacteristic G) ↔ IsQTKEModel G := by
  apply classification_of_theoremsD_and_E hna hK hD
  intro hG T hmany hempty
  exact Chapter15.source_theoremE_of_MS_fields_and_singleton_resolvers
    earlier.rankTwo earlier.linearThree hG T hmany hempty
    (hrank hG T hmany hempty) (hcentral hG T hmany hempty)

end CFSG.Quasithin
