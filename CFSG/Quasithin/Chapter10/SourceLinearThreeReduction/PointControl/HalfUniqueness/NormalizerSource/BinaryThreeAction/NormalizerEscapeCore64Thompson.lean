module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeDoubledThompson
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeJoinCore
public import Stellmacher.BaumannMap
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# The original half-Sylow characteristic subgroups on the full core

The actual core of order sixty-four has injective two-natural coordinates.
Its literal half-Sylow is Sylow in the original component product. The native
Thompson and Baumann calculation therefore applies to these same original
subgroups. Inclusion into G preserves both characteristic constructions and
the relative centralizers, whose orders are sixteen.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 ChapterC.BinaryMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Both characteristic subgroups of the original half-Sylow have a fixed
subgroup of order sixteen on the complete abelian MS core of order sixty-four. -/
theorem normalizerEscape_fullCore64_thompson_baumann_fixed
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : IsMulCommutative (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))))
    (hcard : Nat.card ((commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))).map
        (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))).subtype) = 64) :
    let C := ⁅(localJoin T L).pCoreIn 2,L⁆
    let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
    Nat.card (C ⊓ centralizer (elementaryAbelianMaxJ T₁ : Set G) : Subgroup G) = 16 ∧
      Nat.card (C ⊓ centralizer (ChapterB.baumann T₁ : Set G) : Subgroup G) = 16 := by
  let T₁ := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let J := L ⊔ T₁
  let A := L.subgroupOf J
  let R := T₁.subgroupOf J
  let h := normalizerEscapeBinaryInput D (selected_nonnormal s) hout s.quotient
  have hCcard : Nat.card (commutatorCore A) = 64 := by
    change Nat.card ((commutatorCore A).map J.subtype) = 64 at hcard
    simpa only [card_map_of_injective J.subtype_injective] using hcard
  obtain ⟨m,hm,⟨q⟩⟩ :=
    AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient (h := h) hc
  have hm2 : m = 2 := by
    rcases hm with hm | hm
    · have hb := (h.abelianCore_fixedKernel_bounds hc (Or.inl hm) q).1
      have he := q.card
      rw [hm] at he
      change Nat.card (commutatorCore A) = 2^(3*1) * Nat.card (coreFixed A) at he
      rw [hCcard] at he
      change Nat.card (coreFixed A) ≤ 2 at hb
      norm_num at he
      omega
    · exact hm
  subst m
  have hz : coreFixed A = ⊥ :=
    (eq_bot_iff_card _).mpr (h.abelianCore_fixedKernel_eq_one_of_twoCopies hc q)
  have hi : Function.Injective q.projection :=
    (MonoidHom.ker_eq_bot_iff q.projection).mp (q.kernel.trans hz)
  obtain ⟨P,hP⟩ := halfSylow_sylow_component_join D (selected_nonnormal s)
  have hPR : (P : Subgroup J) = R := by
    apply map_injective J.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  obtain ⟨d⟩ := h.exists_doubledCoreAction hc q hi P hPR.symm.le
  have hd := d.thompson_baumann_fixed_card hc hPR.symm.le
  have hC : ⁅(localJoin T L).pCoreIn 2,L⁆ = (commutatorCore A).map J.subtype :=
    normalizerEscape_join_core_component D (selected_nonnormal s) hout s.quotient
  have hR : R.map J.subtype = T₁ := map_subgroupOf_eq_of_le le_sup_right
  have hTh : (elementaryAbelianMaxJ R).map J.subtype = elementaryAbelianMaxJ T₁ := by
    rw [←elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective,hR]
  have hBa : (ChapterB.baumann R).map J.subtype = ChapterB.baumann T₁ := by
    change (R ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ R) : Set J)).map
      J.subtype = T₁ ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ T₁) : Set G)
    rw [baumann_map_injective J.subtype J.subtype_injective,hR]
  dsimp only
  rw [hC,←hTh,←hBa,map_inf_centralizer_of_injective J.subtype J.subtype_injective,
    map_inf_centralizer_of_injective J.subtype J.subtype_injective,
    card_map_of_injective J.subtype_injective,card_map_of_injective J.subtype_injective]
  exact hd

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
