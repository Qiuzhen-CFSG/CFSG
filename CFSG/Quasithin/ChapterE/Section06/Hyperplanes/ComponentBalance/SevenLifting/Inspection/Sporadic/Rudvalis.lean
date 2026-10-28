module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Rudvalis
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.Representatives
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# The Rudvalis seven-subgroup inspection from its second centralizer

Every automorphism is inner by the proved stabilizer-class and permutation
normalizer calculations. The actual involution coverage has two classes;
the first centralizer has order 245760, which is not divisible by 2520.
Only nondivisibility by nine of the second literal centralizer remains.
It is a concrete marked model input, weaker than the full E₄ × Sz(8)
structure. This conditional theorem does not assert that input is proved.

Source: Aschbacher–Smith, E.6.18 and 16.1.5(11), printed pp.252,1172.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection

/-- All Ru action and 2A inputs are discharged; only the concrete second
involution centralizer's nine-divisibility exclusion remains. -/
theorem rudvalis_of_second_centralizer
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ¬ IsMulCommutative S) (e : S ≃* Rudvalis.Model)
    (hsecond : ¬ 9 ∣ Nat.card (Rudvalis.InvolutionCentralizers.Centralizer Rudvalis.a)) :
    SevenActionInspection S := by
  let : IsSimpleGroup Rudvalis.Model := (MulEquiv.isSimpleGroup_congr e).mp inferInstance
  have hncR : ¬ IsMulCommutative Rudvalis.Model := by
    intro h
    let := h
    apply hnc
    constructor
    constructor
    intro x y
    apply e.injective
    simp only [map_mul]
    exact IsMulCommutative.is_comm.comm _ _
  have hz : center Rudvalis.Model = ⊥ := by
    rcases (inferInstance : (center Rudvalis.Model).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (hncR (center_eq_top_iff.mp ht)).elim
  apply of_equiv e
  apply of_involution_fixed_card
  intro a ha
  obtain ⟨g,rfl⟩ := Chapter1.XiEmbedding.OuterModels.rudvalis_conj_surjective a
  have hg : orderOf g = 2 := by
    rw [← orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hz)]
    exact ha
  rw [MulAut.fixedSubgroup_conj]
  rcases Rudvalis.InvolutionCentralizers.centralizer_representatives g hg with h | h
  · change ¬ 2520 ∣ Nat.card (Rudvalis.InvolutionCentralizers.Centralizer g)
    rw [Rudvalis.InvolutionCentralizers.first_centralizer_card h.1]
    decide
  · obtain ⟨f⟩ := h.2
    rw [Nat.card_congr f.toEquiv]
    exact fun hd => hsecond ((by decide : 9 ∣ 2520).trans hd)
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SporadicInspection
