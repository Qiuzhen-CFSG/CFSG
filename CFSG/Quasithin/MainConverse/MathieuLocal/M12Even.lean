module

public import Theory.Mathieu.M12.SmallParabolicPair.ElementaryNormalizerCover
public import CFSG.Quasithin.Defs

/-!
# Even characteristic for the M₁₂ converse case

The fixed marked Sylow subgroup has four possible normal elementary abelian
subgroups. Their normalizers are the two marked parabolics and two elementary
normalizers. The intrinsic two-cores of the parabolics and elementary
normalizers are self-centralizing, so the maximal-local elementary-normalizer
reduction proves condition (E).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(5), printed pp.3–4 and 481–482; concrete M₁₂ local data from Lemma
14.2.21, printed p.988.
-/

namespace CFSG.Quasithin.MainConverse

open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair

private theorem characteristicTwo_normalizer_of_selfCentralizing
    {G : Type*} [Group G] (A : Subgroup G) (hp : IsPGroup 2 A)
    (hc : centralizer (A : Set G) ≤ A) :
    HasCharacteristicTwo (normalizer (A : Set G)) := by
  have hA : A.subgroupOf (normalizer (A : Set G)) ≤
      pCore 2 (normalizer (A : Set G)) :=
    le_sSup ⟨inferInstance, hp.of_equiv (subgroupOfEquivOfLe A.le_normalizer).symm⟩
  intro g hg
  apply hA
  apply hc
  intro x hx
  exact congrArg Subtype.val (hg ⟨x, A.le_normalizer hx⟩ (hA hx))

/-- The actual M₁₂ carrier has even characteristic. -/
public theorem m12_evenCharacteristic : IsEvenCharacteristic M12 := by
  apply IsEvenCharacteristicAt.all (T := commonSylow)
  intro M hM hSM
  rcases EvenLocal.maximal_local_cases M hM hSM with rfl | rfl | rfl | rfl
  · exact firstParabolic_pCore_selfCentralizing
  · exact secondParabolic_pCore_selfCentralizing
  · exact characteristicTwo_normalizer_of_selfCentralizing EvenLocal.pureElementary
      (IsElementaryAbelian.isPGroup 2 _) EvenLocal.centralizer_pure.le
  · exact characteristicTwo_normalizer_of_selfCentralizing elementary
      (IsElementaryAbelian.isPGroup 2 _) centralizer_elementary_eq.le

end CFSG.Quasithin.MainConverse
