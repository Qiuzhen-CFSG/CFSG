module
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ThreePart
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Rudvalis
public import Theory.GroupTheory.AutomorphismTowerSimple
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.Reduction

/-!
# The actual Rudvalis fixed-component exclusion in E.6.23

Both literal involution centralizers have order indivisible by nine. Innerness
of automorphisms and actual involution-class transport therefore exclude an
A₆ component in an involution fixed subgroup. The source wrapper applies this
to the original Y/Z(Y), carrying its actual involution and component together.
Simplicity and perfectness of the model are inherited from that source quotient.
Source: Aschbacher–Smith, Quasithin E.6.23 and 16.1.5(11), pp.254,1172.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic
public theorem rudvalis [IsSimpleGroup Rudvalis.Model] [Group.IsPerfect Rudvalis.Model] :
    FixedSixExclusion Rudvalis.Model := by
  have hnc : ¬ IsMulCommutative Rudvalis.Model :=
    Group.IsPerfect.not_isMulCommutative Rudvalis.Model
  have hz : center Rudvalis.Model = ⊥ := by
    rcases (inferInstance : (center Rudvalis.Model).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (hnc (center_eq_top_iff.mp ht)).elim
  apply FixedSixExclusion.of_fixed_card
  intro a ha
  obtain ⟨g,rfl⟩ := Chapter1.XiEmbedding.OuterModels.rudvalis_conj_surjective a
  have hg : orderOf g = 2 := by
    rw [←orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hz)]
    exact ha
  rw [MulAut.fixedSubgroup_conj]
  exact fun hd => Rudvalis.InvolutionCentralizers.centralizer_not_nine g hg
    ((by decide : 9 ∣ 360).trans hd)

public theorem rudvalis_source {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M V : Subgroup G) [IsElementaryAbelian 2 V] :
    SourceExclusion Rudvalis.Model T M V :=
  sourceExclusion_of_fixed_exclusion (fun hs hp => by
    let := hs
    let := hp
    exact rudvalis) T M V
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic
