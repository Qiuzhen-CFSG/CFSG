module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Characteristic
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SourceOutside
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# The conditional parabolic contradiction in original 15.1.29

The Sylow distinction makes T normalize Q₂. A nontrivial characteristic
subgroup C of Q₂ normal in KQ₂ is therefore normalized by KT. The original
factorization M=⟨Y₀,T⟩C_M(V) and A.5.7 put N_G(C), hence K, in M.
But K is perfect, so the proved empty-Lf residual theorem makes K fix V.
This contradicts [V₂,Y₀]=V₂, since V₂ has order four.

The final theorem uses the actual natural-module recognition to recover
the same NineSource, and C.1.34 to produce C. Construction of the three
parabolics and their rank-two local input is still explicit. In particular
this conditional implication does not assert that 15.1.29 is complete.

Source: Aschbacher--Smith, 15.1.29, printed pp.1103--1104.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterA.Section05To06 Section03 Section03.InitialSource
open Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The final characteristic-subgroup/maximal-local argument. Normality
of C is only required inside KQ₂, never inside the ambient simple group. -/
theorem false_of_natural_parabolics_characteristic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    {d : CaseIComponentData T M Mc V} (s : d.NineSource)
    {p : NaturalParabolics d} (a : NaturalParabolicGeometry p)
    (C : Subgroup p.Q2) (hC : C.Characteristic) (hne : C ≠ ⊥)
    (hn : ((C.map p.Q2.subtype).subgroupOf (p.K ⊔ p.Q2)).Normal) : False := by
  let := hC
  let := a.perfect
  have hYM : p.Y0 ≤ M := (map_subtype_le _).trans a.first_le
  have hXM : p.Y0 ⊔ (T : Subgroup G) ≤ M := sup_le hYM hM.1.2
  have hcover : OrderingLE T M (p.Y0 ⊔ (T : Subgroup G)) := by
    intro m hm
    obtain ⟨x,hx,c,hc,he⟩ := a.product m hm
    refine ⟨x,⟨hXM hx,hx⟩,c,⟨hc.1,?_⟩,he⟩
    change c ∈ centralizer (localModule T M : Set G)
    exact (centralizer_le hfull.ge) hc.2
  have hCN : (T : Subgroup G) ≤ normalizer (C.map p.Q2.subtype : Set G) :=
    (a.normalizes_second_core s.toExchangedSource hM h).trans
      (normalizer_le_normalizer_characteristic_image p.Q2 C)
  have hCKQ : C.map p.Q2.subtype ≤ p.K ⊔ p.Q2 :=
    (map_subtype_le _).trans le_sup_right
  have hKN : p.K ≤ normalizer (C.map p.Q2.subtype : Set G) :=
    le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer hCKQ).mp hn)
  have hNM : normalizer (C.map p.Q2.subtype : Set G) ≤ M := by
    apply normalizer_le_of_unique_maximalTwoLocal
      (fun N hN hXN => (lemma_A_5_7_1 hM le_sup_right hXM hcover N hN).mp hXN)
      (((isPGroup_pCoreIn 2 p.P2).to_subgroup C).map p.Q2.subtype)
    · exact fun he => hne ((C.map_eq_bot_iff_of_injective p.Q2.subtype_injective).mp he)
    · exact sup_le (le_sup_left.trans hKN) hCN
  have hKV : p.K ≤ centralizer (V : Set G) :=
    (perfect_subgroup_centralizes_localModule hG T hempty hM (hKN.trans hNM)).trans
      (centralizer_le hfull.le)
  have hV2V : d.nineMovingPlane ≤ V := le_sup_right.trans_eq s.planes_sup
  have hYV2 : p.Y0 ≤ centralizer (d.nineMovingPlane : Set G) :=
    (le_sup_left.trans hKV).trans (centralizer_le hV2V)
  have hbot : d.nineMovingPlane = ⊥ := by
    rw [← a.moving, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hYV2
  have hc := s.moving_card
  rw [hbot, card_bot] at hc
  omega

/-- The natural recognition on the original component supplies the Nine
row; the full earlier C.1.34 input then supplies the characteristic subgroup.
The two geometric premises remain source-construction obligations. -/
theorem false_of_natural_parabolics
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (d : CaseIComponentData T M Mc V) (hlinear : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hnatural : d.HasNaturalMovedModule t)
    (p : NaturalParabolics d) (a : NaturalParabolicGeometry p)
    (b : NaturalRankTwoInput p)
    (hMS : NaturalParabolicMSClassification G) : False := by
  have s := hlinear.1.nineSource_of_natural_moved_module hM hu h t ht htS hnatural
  obtain ⟨C,hC,hne,hn⟩ := b.exists_characteristic_normal hMS
  exact false_of_natural_parabolics_characteristic hG hempty hM h hfull s a C hC hne hn

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
