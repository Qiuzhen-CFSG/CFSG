module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Orders
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.TripleHeptad
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalM23.Local

/-!
# Original triple marking and local cubic fusion at the Chapter 12 consumer

The ChosenModule supplies the generic input on the whole reduced subgroup.
The original nonmaximal linear branch selects its exceptional overcomponent.
The same quotient marking retains the pair and identifies M ∩ J as the
triple stabilizer. One native heptad equivalence preserves all of these
subgroups and the full two-core. The intersection has index five in M, giving the original local orders
and fusing every cubic in M ∪ J in the ambient group.

Source: Aschbacher–Smith 5.2.11(2),(3), 5.2.14(2), printed pp.653–654
(`refs/quasithin.pdf`). The ΓL₂(4) identification, cubic-normalizer recognition,
compatible completion, and ambient M₂₃ recognition remain to be proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
open Sporadic.Mathieu.M23Geometry
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

theorem rankOne_global_linear_nonmaximal_pair_triple_marking
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
      ∃ e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7),
        ∃ (i j : Fin 7) (s : Finset (Fin 7)), i ≠ j ∧ s.card = 3 ∧ i ∈ s ∧ j ∈ s ∧
          let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
          (residual H).subgroupOf J =
            (fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7))).comap q ∧
          H.subgroupOf J =
            (MulAction.stabilizer (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7))).comap q ∧
          (normalizer (L : Set G)).subgroupOf J =
            (MulAction.stabilizer (alternatingGroup (Fin 7)) (s : Set (Fin 7))).comap q := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨_,hc⟩ := d.linear_maximal_or_exceptional hi hH hp F hm hF he
  obtain ⟨_,J,hJ,hKJ,_⟩ := hc.resolve_left hnonmax
  exact ⟨J,hJ,hKJ,d.linear_exceptional_pair_triple_marking hi hH hp F hm hF he hJ hKJ⟩

theorem rankOne_global_linear_nonmaximal_local_orders_and_cubic_fusion
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
      Nat.card (normalizer (L : Set G) ⊓ J : Subgroup G) = 1152 ∧
      (normalizer (L : Set G) ⊓ J).relIndex (normalizer (L : Set G)) = 5 ∧
      Nat.card (normalizer (L : Set G)) = 5760 ∧
      Nat.card ((normalizer (L : Set G)) ⧸ pCore 2 (normalizer (L : Set G))) = 360 ∧
      ∀ a b : G, orderOf a = 3 → orderOf b = 3 →
        (a ∈ normalizer (L : Set G) ∨ a ∈ J) →
        (b ∈ normalizer (L : Set G) ∨ b ∈ J) → IsConj a b := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨_,hc⟩ := d.linear_maximal_or_exceptional hi hH hp F hm hF he
  obtain ⟨_,J,hJ,hKJ,_⟩ := hc.resolve_left hnonmax
  obtain ⟨hindex,hM,hquot⟩ := d.linear_exceptional_left_orders hi hH hp F hm hF he hJ hKJ
  exact ⟨J,hJ,hKJ,d.linear_exceptional_intersection_card hi hH hp F hm hF he hJ hKJ,
    hindex,hM,hquot,d.linear_exceptional_local_cubics_isConj hi hH hp F hm hF he hJ hKJ⟩

theorem rankOne_global_linear_nonmaximal_pair_triple_heptad_marking
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
      ∃ (ζ : J ≃* heptadStabilizer) (t : Finset (Fin 7)),
        t.card = 3 ∧ (5 : Fin 7) ∈ t ∧ (6 : Fin 7) ∈ t ∧
        (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
        ((residual H).subgroupOf J).map ζ.toMonoidHom =
          (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
        (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
        ((normalizer (L : Set G)).subgroupOf J).map ζ.toMonoidHom =
          (MulAction.stabilizer (Equiv.Perm (Fin 7)) (t : Set (Fin 7))).comap heptadAction := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨_,hc⟩ := d.linear_maximal_or_exceptional hi hH hp F hm hF he
  obtain ⟨_,J,hJ,hKJ,_⟩ := hc.resolve_left hnonmax
  exact ⟨J,hJ,hKJ,d.linear_exceptional_pair_triple_heptad_marking hi hH hp F hm hF he hJ hKJ⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
