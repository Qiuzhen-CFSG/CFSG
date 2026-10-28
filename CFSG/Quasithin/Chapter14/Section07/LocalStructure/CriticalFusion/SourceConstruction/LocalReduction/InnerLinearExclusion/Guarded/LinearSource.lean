module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.LinearSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.SystemGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction

/-!
# Original small-quotient exclusion: LinearSource

The source proof is specialized to the same G,T structural and escape inputs.
All subgroup restrictions, quotient maps and the actual rank-three system
are retained. The universal public API in the original module is unchanged.
Source: Aschbacher–Smith 14.7.11,49, printed pp.1045–1046,1064,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A₃ recognition determines the literal local two-core's order. -/
private theorem a3_point_core_card {X : Type*} [Group X] [Finite X] (S : DSystem .A3 X) :
    Nat.card (pCore 2 (S.family 0)) = 8 := by
  have hG : Nat.card X = 20160 :=
    (Nat.card_congr S.a3_source_recognition.some.toEquiv).trans Matrix.PSL4Two.card_model
  have hQ : Nat.card (S.family 0 ⧸ pCore 2 (S.family 0)) = 168 :=
    (Nat.card_congr (S.point_A3 rfl).some.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hlocal := (pCore 2 (S.family 0)).card_mul_index
  have hglobal := (S.family 0).card_mul_index
  change Nat.card (S.family 0) * Nat.card S.Point = Nat.card X at hglobal
  change Nat.card (pCore 2 (S.family 0)) * Nat.card (S.family 0 ⧸ pCore 2 (S.family 0)) = Nat.card (S.family 0) at hlocal
  rw [S.a3_points_card,hG] at hglobal
  rw [hQ] at hlocal
  omega

/-- The L₃(2) full-quotient case of original 14.7.11. Recognition bounds
O₂(I) by the eight-element seed, forcing I to normalize that seed and
contradicting its original escape. -/
theorem small_local_linearThree_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : Chapter14.Section04.LargerDimension.LocalAction.Components.EarlierFaithfulClassification G (T : Subgroup G))
    (hmovement : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (he : Nonempty (HStar I ≃* Matrix.PSL3Two.PSL)) : False := by
  obtain ⟨H₂,h₂,S,hS⟩ := small_local_source_system h hab structural previous faithful
    hmovement I hI .A3 (fun _ => he) (by simp)
  let E := (L ⊔ (T : Subgroup G)) ⊔ I
  have hS0 : S.family 0 = I.subgroupOf E := by rw [hS]; rfl
  let e := (MulEquiv.subgroupCongr hS0).trans (subgroupOfEquivOfLe (show I ≤ E from le_sup_right))
  have hcard : Nat.card (pCore 2 I) = 8 := by
    let c := ((pCore 2 (S.family 0)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
    exact (Nat.card_congr c.toEquiv).symm.trans (a3_point_core_card S)
  have hQcard : Nat.card (I.pCoreIn 2) = 8 := by
    exact (Nat.card_congr ((pCore 2 I).equivMapOfInjective I.subtype I.subtype_injective).toEquiv).symm.trans hcard
  have hVQ : V ≤ I.pCoreIn 2 :=
    (le_conjugateSpanBy V I).trans (WholeResidualAssembly.local_f9_hypothesis_at h structural hab I hI).UH_le_QH
  have hV : V = I.pCoreIn 2 := eq_of_le_of_card_ge hVQ (by rw [hQcard,h.seed_card]; decide)
  apply hI.2.2
  apply le_trans _ (h.seed_normalizer_le_at structural)
  rw [hV]
  exact I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
