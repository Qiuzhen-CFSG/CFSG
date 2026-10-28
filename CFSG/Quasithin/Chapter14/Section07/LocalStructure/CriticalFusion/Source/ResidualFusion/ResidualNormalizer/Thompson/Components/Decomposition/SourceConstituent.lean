module

public import CFSG.Quasithin.Chapter12.Section02.ChosenModule.InsideReducedWitness
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.Decomposition.GlobalOffender.Source
public import CFSG.Quasithin.Chapter13.Section03.PlaneNoncentralitySource.Classification
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness
public import Theory.GroupTheory.CentralPChiefFactorsOddQuotient

/-!
# Original homogeneous constituents inside the residual moved span

The literal span [E,B] lies in B, is elementary and normal in BT, and is
generated again by its commutators with B. The intrinsic two-core of B
centralizes it. A.4.11 constructs a reduced sub-witness inside this span;
A.1.42 then selects an original ChosenModule without leaving the span.
We do not assert that the whole [E,B] is reduced in BT.

In the A₅ branch, the genuine earlier 13.3.2 module implication identifies
this selected constituent with the alternating natural module of order16.
All source quotient maps and the original component B are retained. The
comparison between this constituent and the full B.5 moved section remains
separate from this existence and source-classification application.

Source: Aschbacher–Smith 14.7.67(4), printed p.1070; 14.3.4(3), p.990;
13.3.2(3), p.885; A.4.11 and A.1.42.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter12.Section02 ResidualNormalizer
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

private theorem central_two_chief_of_quasisimple
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q] : HasCentralPChiefFactors 2 Q := by
  let e : (Q ⧸ (⊥ : Subgroup Q)) ≃* Q := QuotientGroup.quotientBot
  let : IsQuasisimple (Q ⧸ (⊥ : Subgroup Q)) := IsQuasisimple.of_mulEquiv e.symm
  exact hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
    (⊥ : Subgroup Q) (by simp) inferInstance

/-- A genuine original homogeneous constituent inside the specified moved span. -/
theorem Data.residual_component_chosen_in_moved_span
    (d : Data T L V F W)
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F)) :
    ∃ U : Subgroup G, Nonempty (ChosenModule T B U) ∧ U ≤ ⁅E F,B⁆ := by
  let H := B ⊔ (T : Subgroup G)
  let A := B.subgroupOf H
  let C := ⁅E F,B⁆
  have hl := d.residual_component_mem_localFamily hs hB
  let : Group.IsPerfect B := Chapter1.mem_L_isPerfect hl
  have hpB := Chapter1.Section02.Adequate.mem_L_isPPerfect hl
  have hnB := d.residual_T_normalizes_component earlier hs hB
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hnB)
  have hBN := residual_component_in_normalizer hB
  have hn := (normal_subgroupOf_iff_le_normalizer hBN.1).mp
    (d.residual_component_normal_in_normalizer earlier hs hB)
  have hEB : E F ≤ normalizer (B : Set G) :=
    d.residualSpan_le_D.trans (D_le_normalizer.trans hn)
  have hBE : B ≤ normalizer (E F : Set G) :=
    (hB.1.trans J_le_Y).trans d.residual_Y_normalizes_E
  have hCB : C ≤ B := le_normalizer_iff_commutator_le_right.mp hEB
  have hCE : C ≤ E F := le_normalizer_iff_commutator_le_left.mp hBE
  have hCH : C ≤ H := hCB.trans le_sup_left
  let D := C.subgroupOf H
  have hHC : H ≤ normalizer (C : Set G) := by
    intro t ht
    have htE : t ∈ normalizer (E F : Set G) :=
      sup_le hBE d.residual_T_normalizes_E ht
    have htB : t ∈ normalizer (B : Set G) := sup_le B.le_normalizer hnB ht
    apply (mem_normalizer_iff_map_conj_eq).mpr
    dsimp only [C]
    rw [map_commutator,
      (mem_normalizer_iff_map_conj_eq.mp htE),
      (mem_normalizer_iff_map_conj_eq.mp htB)]
  let : D.Normal := normal_subgroupOf_of_le_normalizer hHC
  let := d.residualSpan_elementary hs
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le hCE
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf hCH
  have hCne : C ≠ ⊥ := by
    change ⁅E F,B⁆ ≠ ⊥
    rw [commutator_comm]
    exact fun he => d.residual_component_not_centralizes hB
      (commutator_eq_bot_iff_le_centralizer.mp he)
  have hDC : D.map H.subtype = C := map_subgroupOf_eq_of_le hCH
  have hAB : A.map H.subtype = B := map_subgroupOf_eq_of_le le_sup_left
  have hm : ⁅D,A⁆ ≠ ⊥ := by
    intro he
    have he' := congrArg (map H.subtype) he
    rw [map_commutator,hDC,hAB,Subgroup.map_bot] at he'
    have hi : ⁅C,B⁆ = C :=
      commutator_isPPerfect_idempotent B (E F) hpB
        (IsElementaryAbelian.isPGroup 2 (E F)) hBE
    exact hCne (hi.symm.trans he')
  let e : A ≃* B := subgroupOfEquivOfLe le_sup_left
  have hpA : IsPPerfect 2 A := hpB.of_surjective e.symm.toMonoidHom e.symm.surjective
  let : IsQuasisimple (residualOffenderComponent (L := L) (F := F) B) :=
    d.residualOffenderComponent_quasisimple earlier hs hB
  let : IsQuasisimple (B ⧸ pCore 2 B) :=
    IsQuasisimple.of_mulEquiv (residualComponentOffenderEquiv hB).symm
  let eQ := QuotientGroup.congr (pCore 2 A) (pCore 2 B) e (pCore_map_iso 2 e)
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eQ.symm
  have hchief : HasCentralPChiefFactorsAbove 2 (pCore 2 A) :=
    (hasCentralPChiefFactorsAbove_iff_quotient _).mpr central_two_chief_of_quasisimple
  have hkill : (pCore 2 A).map A.subtype ≤ centralizer (D : Set H) := by
    intro a ha v hv
    apply Subtype.ext
    have hcore : (a : G) ∈ B.pCoreIn 2 := by
      have hm := mem_map_of_mem H.subtype ha
      change (a : G) ∈ (A.pCoreIn 2).map H.subtype at hm
      rw [map_pCoreIn_of_injective 2 A H.subtype H.subtype_injective,hAB] at hm
      exact hm
    exact d.residual_component_core_centralizes hs hB hcore v (hCE hv)
  obtain ⟨R,hRD,hR,hmR⟩ := ChapterA.Section04.exists_reduced_witness_of_moved
    A D (inferInstance : A.Normal).isSubnormal hpA hchief hm hkill
  obtain ⟨U,hU,hu⟩ := exists_chosen_le_reduced_witness hnB R hR hmR
  exact ⟨U,hU,hu.trans ((map_mono hRD).trans_eq hDC)⟩

/-- The actual alternating constituent in the A₅ branch, with the relative
Sylow supplied by the original structural and uniqueness theorems. -/
theorem Data.residual_component_alternating_constituent_of_source
    (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (earlier : EarlierFaithfulClassification G (T : Subgroup G))
    (modules : Chapter13.Section03.PlaneNoncentralitySource.AlternatingFiveModules1332.{u})
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (hfive : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))) :
    ∃ U : Subgroup G, Nonempty (ChosenModule T B U) ∧ U ≤ ⁅E F,B⁆ ∧
      Chapter6.Source.IsConjugationModel B U Chapter6.Source.a5Module ∧ Nat.card U = 16 := by
  have hs := (d.residual_intersections structural uniqueness).2.2.2
  obtain ⟨U,⟨chosen⟩,hle⟩ := d.residual_component_chosen_in_moved_span earlier hs hB
  have hm := modules G T L d.counterexample B (d.residual_component_faithful hs hB)
    hfive U chosen
  exact ⟨U,⟨chosen⟩,hle,hm,
    Chapter13.Section03.PlaneNoncentralitySource.alternatingFive_model_card hm⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
