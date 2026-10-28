module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.SystemGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.A3SourceGeometry
public import Theory.SpecificGroups.ProjectiveLinear.FourTwoPGroupBound

/-!
# The L₃(2) and inner linear exclusions on the selected component

For a full L₃(2) quotient, the actual A₃ system recognizes the generated
subgroup as L₄(2). Its point index and group order make the original
local two-core have order eight. The original seed lies in that core and
also has order eight, so equality forces the local subgroup into N_G(L),
contrary to its escape. This proves the L₃(2) case of 14.7.11.

For an inner L₄(2) or L₅(2) component, the already constructed rank-two
preimages supply an escaping L₃(2) local subgroup. The actual selected
large component supplies point-core movement, so the inner exclusion has
no additional movement premise. The L₃(2) component exclusion retains the
earlier 14.5.21(2) core-commutator identity. All original 14.7.48 data,
relative components, intrinsic quotients and the full catalogue are kept.

The A₆ component exclusion, C₃ contradiction and same-G,T guarded
transport remain required by this task. The graph branch and final
discharge of the genuine earlier-source inputs retain their existing owners.
Source: Aschbacher–Smith, refs/quasithin.pdf, printed pp.1045–1046,
1064–1065; I.5.1(1), printed pp.419–422.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
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
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    (le_conjugateSpanBy V I).trans (local_f9_hypothesis h hab structural previous I hI).UH_le_QH
  have hV : V = I.pCoreIn 2 := eq_of_le_of_card_ge hVQ (by rw [hQcard,h.seed_card]; decide)
  apply hI.2.2
  apply le_trans _ (h.seed_normalizer_le_at (structural G T))
  rw [hV]
  exact I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components
/-- The inner-action branch of 14.7.51 for any actual original component.
The earlier original point-core movement is retained;
the rank-two preimages and their local containment are constructed. -/
theorem local_inner_linear_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hmovement : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : I = K ⊔ (T : Subgroup G)) (hLK : F.Li L 1 ≤ K)
    {m : ℕ} (hm : m = 3 ∨ m = 4) (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) (m + 1) 2)
    (hi : ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K)) : False := by
  obtain ⟨E,_,_,hE,⟨a⟩⟩ := hmodel
  let := Fintype.ofFinite E
  let f : E ≃+* ZMod 2 := (ZMod.ringEquivOfPrime E Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hE)).symm
  let eK := a.trans ((Atlas.fieldEquivPSL (m + 1) f).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < m + 1)))
  obtain ⟨J,hJ,hJI,hBJ,heJ⟩ := local_inner_linear_exists_escaping_linearThree
    d h hab structural previous faithful earlier I K hI hn hgen hLK hm eK hi
  exact small_local_linearThree_impossible h hab structural previous faithful hmovement J hJ heJ

/-- Exclude both inner linear rows on the actual selected component,
without a point-core movement or core-commutator premise. -/
theorem original_exists_component_inner_exclusion
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source48 : ∀ K : Subgroup G, K ≤ F.H → (K.subgroupOf F.H).IsCComponent →
      F.Li L 1 ≤ K ∧ F.H = K ⊔ (T : Subgroup G) ∧ F.UH F.H = ⁅F.UH F.H,K⁆) :
    ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
      (K.subgroupOf F.H).Normal ∧ ¬ K ≤ normalizer (L : Set G) ∧
      Models.F918Models (K ⧸ pCore 2 K) ∧ SylowOvergroupComponentUnique K ∧
      F.Li L 1 ≤ K ∧ F.H = K ⊔ (T : Subgroup G) ∧ F.UH F.H = ⁅F.UH F.H,K⁆ ∧
      (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 →
        Nonempty (HStar F.H ≃* Matrix.PSL3Two.PSL)) ∧
      ∃ hn : (T : Subgroup G) ≤ normalizer (K : Set G),
        ∀ m : ℕ, (m = 3 ∨ m = 4) → ClassicalGroup.IsPSL (K ⧸ pCore 2 K) (m + 1) 2 →
          ¬ (∀ (t : G) (ht : t ∈ (T : Subgroup G)),
            (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
              MulAut.innerSubgroup (K ⧸ pCore 2 K)) := by
  obtain ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,hthree,hn,hinner⟩ :=
    original_exists_component_quotient_reduction d h hab structural previous faithful earlier source48
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  refine ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,hthree,hn,?_⟩
  intro m hm hmodel hi
  exact local_inner_linear_impossible d h hab structural previous faithful earlier
    (selected_large_component_plane_moved_at h (structural G T) (previous G T) faithful
      K hKH hK (Or.inr ⟨m,hm,hmodel⟩)) F.H K hH hn hgen hLK hm hmodel hi

/-- On the component actually selected by the original normal-component
reduction, exclude the L₃(2) row and both inner linear rows. The retained
14.5.21(2) identity discharges movement in the small row. The A₆ and graph
rows retain their separate remaining duties. -/
theorem original_exists_component_linear_exclusions
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (core_commutator : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (source48 : ∀ K : Subgroup G, K ≤ F.H → (K.subgroupOf F.H).IsCComponent →
      F.Li L 1 ≤ K ∧ F.H = K ⊔ (T : Subgroup G) ∧ F.UH F.H = ⁅F.UH F.H,K⁆) :
    ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
      (K.subgroupOf F.H).Normal ∧ ¬ K ≤ normalizer (L : Set G) ∧
      Models.F918Models (K ⧸ pCore 2 K) ∧ SylowOvergroupComponentUnique K ∧
      F.Li L 1 ≤ K ∧ F.H = K ⊔ (T : Subgroup G) ∧ F.UH F.H = ⁅F.UH F.H,K⁆ ∧
      ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 ∧
      ∃ hn : (T : Subgroup G) ≤ normalizer (K : Set G),
        ∀ m : ℕ, (m = 3 ∨ m = 4) → ClassicalGroup.IsPSL (K ⧸ pCore 2 K) (m + 1) 2 →
          ¬ (∀ (t : G) (ht : t ∈ (T : Subgroup G)),
            (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
              MulAut.innerSubgroup (K ⧸ pCore 2 K)) := by
  obtain ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,hthree,hn,hinner⟩ :=
    original_exists_component_inner_exclusion d h hab structural previous faithful earlier source48
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  have hm := plane_moved_of_core_commutator h core_commutator
  refine ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,?_,hn,?_⟩
  · intro hmodel
    exact small_local_linearThree_impossible h hab structural previous faithful hm F.H hH (hthree hmodel)
  · exact hinner

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
