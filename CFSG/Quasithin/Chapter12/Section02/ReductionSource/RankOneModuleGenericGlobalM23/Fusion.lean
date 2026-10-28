module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.CubicFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.Local

/-!
# Original involution and cubic fusion at the Chapter 12 consumer

Specialize the rank-one generic input using the original ChosenModule and
its whole reduced subgroup. The prepared whole-residual linear comparison
then gives one ambient involution class, source 5.2.14(1), and actual local
cubic fusion. Commuting-pair fusion conjugates involutions inside each
cubic centralizer. The chosen exceptional local is selected
from the original nonmaximal branch and all its cubics have commuting
involutions in that same local.

These apply Aschbacher–Smith 5.2.13–14, printed p.654, and the fusion input
to 5.2.15 (`refs/quasithin.pdf`). They are source increments toward the
ambient M₂₃ recognition and do not assert GlobalExit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Source 5.2.13 at the literal Chapter 12 nonmaximal linear row. -/
theorem rankOne_global_linear_nonmaximal_involutions_isConj
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2) : IsConj s t := by
  exact d.linear_nonmaximal_involutions_isConj
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hnonmax hs ht

/-- Source 5.2.14(1), retaining actual commuting involutions. -/
theorem rankOne_global_linear_nonmaximal_cubics_isConj
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    {a b : G} (ha : orderOf a = 3) (hb : orderOf b = 3)
    (ha2 : ∃ x : G, orderOf x = 2 ∧ Commute a x)
    (hb2 : ∃ x : G, orderOf x = 2 ∧ Commute b x) : IsConj a b := by
  exact d.linear_nonmaximal_cubics_isConj
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hnonmax ha hb ha2 hb2

/-- Cubics fuse inside each original involution centralizer. -/
theorem rankOne_global_linear_nonmaximal_involution_centralizer_cubics_isConj
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    (t : G) (ht : orderOf t = 2)
    (a b : centralizer ({t} : Set G)) (ha : orderOf a = 3) (hb : orderOf b = 3) : IsConj a b := by
  exact d.linear_nonmaximal_involution_centralizer_cubics_isConj
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hnonmax t ht a b ha hb

/-- The cubic-centralizer involution-fusion input for source 5.2.15. -/
theorem rankOne_global_linear_nonmaximal_cubic_centralizer_involutions_isConj
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    (c : G) (hc3 : orderOf c = 3)
    (s t : centralizer ({c} : Set G)) (hs : orderOf s = 2) (ht : orderOf t = 2) : IsConj s t := by
  exact d.linear_nonmaximal_cubic_centralizer_involutions_isConj
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hnonmax c hc3 s t hs ht

/-- The chosen exceptional local has actual commuting involutions for all
its cubics, which are fused in the original ambient group. -/
theorem rankOne_global_linear_nonmaximal_exceptional_cubic_fusion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    : ∃ J ∈ Chapter1.LStar G (T : Subgroup G), residual H < J ∧
      (∀ c : J, orderOf c = 3 → ∃ z : J, orderOf z = 2 ∧ Commute c z) ∧
      (∀ a b : J, orderOf a = 3 → orderOf b = 3 → IsConj (a : G) (b : G)) := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨_,hc⟩ := d.linear_maximal_or_exceptional hi hH hp F hm hF he
  obtain ⟨_,J,hJ,hKJ,_⟩ := hc.resolve_left hnonmax
  exact ⟨J,hJ,hKJ,
    fun c hc => d.linear_exceptional_cubic_centralizes_involution hi hH hp F hm hF he hJ hKJ c hc,
    fun a b ha hb => d.linear_nonmaximal_exceptional_cubics_isConj hi hH hp F hm hF he hnonmax hJ hKJ a b ha hb⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
