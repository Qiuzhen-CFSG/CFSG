module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Criteria
public import CFSG.Quasithin.ClassificationModels.Families
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.RankReduction
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.EvenSetup
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.ThreeSubgroup
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.FiveSubgroup
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.Max6Core
public import Theory.SpecificGroups.Rudvalis.Model.Order

/-!
# Quasithinness and even characteristic of the Rudvalis group

The concrete degree-4060 ATLAS model is strongly quasithin. Its certified order
and nonabelian subgroups of orders 27 and 125 give the Sylow rank bounds at
three and five; every other odd prime cube is excluded by the order.

Every central involution of the fixed ambient Sylow is the marked involution,
whose exact centralizer is conjugate to the actual max6 subgroup. Its intrinsic
two-core is self-centralizing, so the Sylow-local centralizer criterion proves
condition E for every required maximal two-local.

All concrete premises are discharged below, giving QT and E across the exact
catalogue equivalence without additional local data, simplicity, nonabelianness
or proper-K premises. The conditional assembly is preserved as a separate API.
The six-sporadic assembly remains with the parent SporadicLocal module.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed p.4, repeated as
Theorem 0.1.1(5), p.482; GLS3 Table 5.3r, p.279.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal

/-- Explicit remaining model calculations imply the Rudvalis QT and E branch. -/
public theorem ru_qt_e_of_local_data
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* ClassificationModels.SporadicName.ru.Carrier)
    (hcard : Nat.card Rudvalis.Model = 145926144000)
    (h3 : ∃ P : Subgroup Rudvalis.Model,
      Nat.card P = 3 ^ 3 ∧ ¬ IsMulCommutative P)
    (h5 : ∃ P : Subgroup Rudvalis.Model,
      Nat.card P = 5 ^ 3 ∧ ¬ IsMulCommutative P)
    (h6 : HasCharacteristicTwo Rudvalis.SylowOvergroups.max6) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  change G ≃* Rudvalis.Model at e
  have hRu := RuRank.stronglyQuasithin_of_subgroups hcard h3 h5
  have hG : IsStronglyQuasithin G := by
    intro p hp ho
    exact (Theory.GroupTheory.primeRank_le_of_injective p e.toMonoidHom e.injective).trans
      (hRu p hp ho)
  exact ⟨hG.quasithin,
    evenCharacteristic_of_model_equiv e (RuEven.evenCharacteristic_of_max6 h6)⟩

/-- Strong quasithinness of the unchanged degree-4060 Rudvalis carrier. -/
public theorem ru_stronglyQuasithin :
    IsStronglyQuasithin ClassificationModels.SporadicName.ru.Carrier :=
  RuRank.stronglyQuasithin_of_subgroups Rudvalis.model_card
    RuRank.three_subgroup RuRank.five_subgroup

/-- Even characteristic of the unchanged degree-4060 Rudvalis carrier. -/
public theorem ru_evenCharacteristic :
    IsEvenCharacteristic ClassificationModels.SporadicName.ru.Carrier :=
  RuEven.evenCharacteristic_of_max6 RuEven.max6_characteristicTwo

/-- The Rudvalis case of QT and E in Theorem 0.1.2(5), transported across
the actual catalogue equivalence with every concrete premise discharged. -/
public theorem ru_qt_e_of_equiv
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* ClassificationModels.SporadicName.ru.Carrier) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ru_qt_e_of_local_data e Rudvalis.model_card
    RuRank.three_subgroup RuRank.five_subgroup RuEven.max6_characteristicTwo

end CFSG.Quasithin.MainConverse.SporadicLocal
