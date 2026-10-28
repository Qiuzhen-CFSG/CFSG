module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.PairContainment
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.C3Source

/-!
# Inner linear exclusion at the original G,T

The original marked point parabolic supplies generating rank-two preimages.
The small L₃(2) quotient is excluded by the literal A₃ system; the product
quotient is excluded by its two invariant cubic lifts. Thus every preimage
lies in the original normalizer, contradicting generation and escape.
Source: Aschbacher–Smith 14.7.49,51, printed pp.1064–1065.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem local_inner_linear_exists_escaping_linearThree
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : I = K ⊔ (T : Subgroup G)) (hLK : F.Li L 1 ≤ K)
    {m : ℕ} (hm : m = 3 ∨ m = 4) (eK : (K ⧸ pCore 2 K) ≃* LinearGroup (m + 1))
    (hi : ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K)) :
    ∃ J : Subgroup G, J ∈ F.Hz L (normalizer (L : Set G)) ∧ J ≤ I ∧
      F.Li L 1 ⊔ (T : Subgroup G) ≤ J ∧
      Nonempty (HStar J ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨e,b,i,_,_,_,_,_,hpre,hall⟩ := local_inner_linear_preimages_at h
    structural I K hI hn hgen hLK (by omega : 2 ≤ m) eK hi
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  let J (j : {j : Fin m // j ≠ i}) :=
    ((cutStabilizer b ({i,j.val} : Set (Fin m))ᶜ).comap q).map I.subtype
  have hout : ∃ j, ¬ J j ≤ normalizer (L : Set G) := by
    by_contra! hallM
    exact hI.2.2 (hall ▸ iSup_le hallM)
  obtain ⟨j,hj⟩ := hout
  have hJI : J j ≤ I := map_subtype_le _
  have hJB : F.Li L 1 ⊔ (T : Subgroup G) ≤ J j := hpre j
  have hJH : J j ≤ F.H := hJI.trans hI.2.1
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hrow : RankTwoQuotient (J j) := rankTwoQuotient_map I.subtype I.subtype_injective _
    (rankTwoQuotient_comap q hq hk _ (twoNode_quotient hm b i j.val j.property.symm))
  have hJ : J j ∈ F.Hz L (normalizer (L : Set G)) := by
    refine ⟨⟨?_,fun _ hx => hJB (hx.elim mem_sup_left mem_sup_right)⟩,hJH,hj⟩
    have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    have hp : F.Vi 1 ≤ (J j).pCoreIn 2 :=
      le_pCoreIn_of_normalizes (IsPGroup.of_card (p := 2) (n := 1) (by simpa using hc))
        ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans hJB))) hJH
    intro hz
    have hb := le_bot_iff.mp (hz ▸ hp)
    simp [hb] at hc
  have hmodel : Nonempty (HStar (J j) ≃* Matrix.PSL3Two.PSL) := by
    rcases hrow with he | ⟨he⟩
    · exact he
    · exact (local_pair_quotient_impossible h hab structural previous faithful (J j) hJ he.some).elim
  exact ⟨J j,hJ,hJI,hJB,hmodel⟩

theorem local_inner_linear_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
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
    h hab structural previous faithful I K hI hn hgen hLK hm eK hi
  exact small_local_linearThree_impossible h hab structural previous faithful hmovement J hJ heJ


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
