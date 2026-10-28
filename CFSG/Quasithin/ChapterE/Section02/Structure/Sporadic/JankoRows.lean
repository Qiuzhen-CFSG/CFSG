module
public import CFSG.Quasithin.ChapterE.Section02.Structure.Sporadic.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoOne.Extension
public import Theory.SpecificGroups.Janko1.Model.NormalizerCentralizerGeneration
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoFour
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.SimpleFittingExtensions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Overlap
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
/-!
# Janko normal-component exclusions

The genuine J1 and J4 inner-automorphism theorems reduce their faithful
normal extensions to the original carriers. Their certified local pairs
contradict minimal parabolicity. The J2 automorphism extension is handled
on its literal degree-100 carrier, using the same two parabolics and the
specified normalizing outer involution.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure.Sporadic
variable {G : Type*} [Group G] [Finite G]

private theorem proper_of_card_lt {M : Type*} [Group M] (P : Subgroup M)
    (h : Nat.card P < Nat.card M) : P ≠ ⊤ := by
  intro he
  exact (ne_of_lt h) (Nat.card_congr ((MulEquiv.subgroupCongr he).trans topEquiv).toEquiv)

theorem no_jankoOne (T : Sylow 2 G) (L : Subgroup G) [IsSimpleGroup L]
    (ha : ¬ IsMulCommutative L) (hF : generalizedFitting G = L)
    (e : L ≃* Janko1.Model) : ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  have ht := ChapterE.JankoOne.socle_eq_top L hF.symm e
  let d : G ≃* Janko1.Model := topEquiv.symm.trans ((MulEquiv.subgroupCongr ht.symm).trans e)
  let : IsSimpleGroup Janko1.Model := e.symm.isSimpleGroup
  have hnc := noncomm_of_equiv L ha e
  have hc := core_eq_bot_of_simple hnc
  have hz : center Janko1.Model = ⊥ := by
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center Janko1.Model)
      inferInstance).resolve_right (fun h => hnc (center_eq_top_iff.mp h))
  obtain ⟨S,has,hjoin⟩ := Janko1.NormalizerCentralizerGeneration.exists_sylow
  have hsp : (S : Subgroup Janko1.Model) ≤ centralizer ({Janko1.a} : Set Janko1.Model) := by
    let := Janko1.SylowTwo.elementary S
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg (fun t : S => (t : Janko1.Model)) (mul_comm' (⟨x,hx⟩ : S) ⟨Janko1.a,has⟩))
  have hp : centralizer ({Janko1.a} : Set Janko1.Model) ≠ ⊤ := by
    intro he
    have hz' : Janko1.a ∈ center Janko1.Model := by
      apply mem_center_iff.mpr
      intro x
      exact mem_centralizer_singleton_iff.mp (show x ∈ centralizer ({Janko1.a} : Set Janko1.Model) from he ▸ trivial)
    exact Janko1.a_ne_one (by simpa only [hz,mem_bot] using hz')
  have hq : normalizer (S : Set Janko1.Model) ≠ ⊤ := by
    intro he
    let : (S : Subgroup Janko1.Model).Normal := normalizer_eq_top_iff.mp he
    have hl : (S : Subgroup Janko1.Model) ≤ pCore 2 Janko1.Model := le_sSup ⟨inferInstance,S.isPGroup'⟩
    have hsbot : (S : Subgroup Janko1.Model) = ⊥ := le_bot_iff.mp (hl.trans hc.le)
    have hcard := Janko1.SylowTwo.card S
    change Nat.card (S : Subgroup Janko1.Model) = 8 at hcard
    rw [hsbot] at hcard
    norm_num at hcard
  exact not_minimal_of_marked_pair T d S _ _ hp hq hsp (S : Subgroup Janko1.Model).le_normalizer hjoin

open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
  Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed in
theorem no_jankoTwo (T : Sylow 2 G) (L : Subgroup G) [IsSimpleGroup L]
    (hF : generalizedFitting G = L) (e : L ≃* Carrier) :
    ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  let : IsSimpleGroup (generalizedFitting G) := (MulEquiv.subgroupCongr hF).isSimpleGroup
  let eF : generalizedFitting G ≃* Carrier := (MulEquiv.subgroupCongr hF).trans e
  rcases SimpleFittingExtensions.ambient_equiv_cases eF with ⟨⟨d⟩⟩ | ⟨⟨d⟩⟩
  · let S := SecondParabolic.sylow FirstParabolic.card_l₁
    apply not_minimal_of_marked_pair T d S l₁ p₂
    · exact proper_of_card_lt _ (by rw [FirstParabolic.card_l₁,FirstParabolic.card_carrier]; decide)
    · exact proper_of_card_lt _ (by rw [PairNormalizer.card_p₂,FirstParabolic.card_carrier]; decide)
    · exact SecondParabolic.s_le_l₁
    · exact PairNormalizer.s_le_p₂
    · exact SecondParabolic.Overlap.l₁_sup_p₂
  · let S := SecondParabolic.outerSylow FirstParabolic.card_l₁
    let P : Subgroup Extension := p₂.map intoExtension ⊔ zpowers outerElement
    have hp : Nat.card P = 2304 := by
      rw [show P = p₂.map intoExtension ⊔ zpowers outerElement from rfl,
        card_sup_zpowers_of_normalizing_involution _ _ SecondParabolic.outerElement_sq
          (fun h => SecondParabolic.outerElement_not_mem_range (p₂.map_le_range intoExtension h))
          SecondParabolic.Overlap.outerElement_normalizes_p₂,
        card_map_of_injective SecondParabolic.intoExtension_injective,PairNormalizer.card_p₂]
    have hjoin : l₁s ⊔ P = ⊤ := by
      rw [FirstParabolic.l₁s_eq_sup_outerElement]
      change (l₁.map intoExtension ⊔ zpowers outerElement) ⊔
        (p₂.map intoExtension ⊔ zpowers outerElement) = ⊤
      rw [sup_sup_sup_comm,sup_idem,← Subgroup.map_sup,SecondParabolic.Overlap.l₁_sup_p₂,
        ← MonoidHom.range_eq_map]
      exact SecondParabolic.Overlap.range_sup_outer FirstParabolic.card_l₁
    exact not_minimal_of_marked_pair T d S l₁s P
      (proper_of_card_lt _ (by rw [FirstParabolic.card_l₁s,SecondParabolic.card_extension FirstParabolic.card_l₁]; decide))
      (proper_of_card_lt _ (by rw [hp,SecondParabolic.card_extension FirstParabolic.card_l₁]; decide))
      (show outerS ≤ l₁s from le_sup_right)
      (sup_le ((map_mono PairNormalizer.s_le_p₂).trans le_sup_left) le_sup_right) hjoin

set_option backward.isDefEq.respectTransparency true in
open Janko4 Janko4.Max1AmalgamRigidity in
theorem no_jankoFour (T : Sylow 2 G) (L : Subgroup G) [IsSimpleGroup L]
    (hF : generalizedFitting G = L) (e : L ≃* Janko4.Model) :
    ¬ ChapterB.IsMinimalParabolicOver T ⊤ := by
  let d := ChapterE.JankoFour.ambientEquiv L hF e
  obtain ⟨S,hSM,hSC⟩ := ChapterE.JankoFour.exists_common_sylow
  have hM : M ≠ ⊤ := proper_of_card_lt _ (by
    change Nat.card (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four) < _
    rw [Cardinality.max1Subgroup_card,Cardinality.model_card]
    decide)
  have hC : C ≠ ⊤ := by
    intro he
    have hHM : H = M := by rw [H_eq_inf,he,inf_top_eq]
    have hh : Nat.card H = 283115520 := by
      rw [card_map_of_injective M.subtype_injective]
      exact Max1RelativeRigidity.pair_centralizer_card
    rw [hHM] at hh
    change Nat.card (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four) = _ at hh
    rw [Cardinality.max1Subgroup_card] at hh
    contradiction
  exact not_minimal_of_marked_pair T d S C M hC hM hSC hSM
    AdequateLocal.centralizer_sup_max1_eq_top
end CFSG.Quasithin.ChapterE.Structure.Sporadic
