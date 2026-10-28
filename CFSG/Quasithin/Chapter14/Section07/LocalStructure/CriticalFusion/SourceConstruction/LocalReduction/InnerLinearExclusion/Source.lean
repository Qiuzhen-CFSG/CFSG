module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Quotients
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Parabolics
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalComponents
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.AlternatingSixQuotient

/-!
# The inner linear branch reduces to an original small local quotient

Apply the full quotient comparison to the actual I = KT. The original
point parabolic selects a node, whose rank-two preimages generate I. If I
escapes N_G(L), one preimage does too. The literal S₃ × S₃ quotient makes
that preimage solvable, so the proved 14.7.29 containment excludes that row.
Thus an escaping preimage has full quotient PSL₃(2).

The final application uses the original normal component selected by
`original_exists_normal_component_reduction`, retains the full F.9.18
catalogue, and takes precisely the earlier 14.7.48 inclusion, generation
and commutator outputs explicitly. Field transport converts the original
PSL predicates to actual binary model isomorphisms. No selected component
is identified with O²(I). The local quotient construction uses same-G,T
12.2.2; the existing component selection and solvable containment APIs still
require their universal earlier inputs.

This is checked progress on Aschbacher–Smith 14.7.49 and the inner branch
of 14.7.51, printed pp.1064–1065, refs/quasithin.pdf. The A₆ full-quotient recovery is also applied to that same selected
component. The original 14.7.11 contradiction remains to be proved; this leaf
does not assert either source exclusion or discharge the graph branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Subgroup Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}


private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

private theorem center_eq_bot_of_linear {Q : Type*} [Group Q] {n : ℕ} (hn : 0 < n)
    (e : Q ≃* LinearGroup n) : center Q = ⊥ := by
  apply Subgroup.card_eq_one.mp
  rw [Nat.card_congr (centerCongr (e.trans (slEquivLinear n).symm)).toEquiv,
    binary_center_eq_bot hn,card_bot]

/-- Construct the full quotient map and all rank-two preimages through the
actual marked point parabolic. Their generation is a conclusion. -/
theorem local_inner_linear_preimages_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : I = K ⊔ (T : Subgroup G)) (hLK : F.Li L 1 ≤ K)
    {m : ℕ} (hm : 2 ≤ m) (eK : (K ⧸ pCore 2 K) ≃* LinearGroup (m + 1))
    (hi : ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K)) :
    ∃ (e : HStar I ≃* LinearGroup (m + 1)) (b : Basis m) (i : Fin m),
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
      (∀ k : K, q (inclusion (hgen ▸ le_sup_left) k) = eK (QuotientGroup.mk' _ k)) ∧
      ((T : Subgroup G).subgroupOf I).map q = cutStabilizer b Set.univ ∧
      ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map q = minimalParabolic b i ∧
      (T : Subgroup G) ≤ normalizer ((F.Li L 1 ⊔ ((T : Subgroup G) ⊓ K) : Subgroup G) : Set G) ∧
      (((F.Li L 1 ⊔ ((T : Subgroup G) ⊓ K)).subgroupOf I).map q = minimalParabolic b i) ∧
      (∀ j : {j : Fin m // j ≠ i},
        F.Li L 1 ⊔ (T : Subgroup G) ≤
          ((cutStabilizer b ({i,j.val} : Set (Fin m))ᶜ).comap q).map I.subtype) ∧
      (⨆ j : {j : Fin m // j ≠ i},
        ((cutStabilizer b ({i,j.val} : Set (Fin m))ᶜ).comap q).map I.subtype) = I := by
  have hz := center_eq_bot_of_linear (by omega : 0 < m + 1) eK
  obtain ⟨_,hPn,hPimage⟩ := inner_point_parabolic_image_at h structural I K hn hgen hLK hz hi
  let e := (innerQuotientEquiv I K hn hgen hz hi).trans eK
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  have hBI : B ≤ I := sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI)
  let c := subgroupOfEquivOfLe hBI
  let eB := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
    (pointQuotientEquiv_at h structural)
  obtain ⟨b,i,hb,hBi,hBpre,hall⟩ := exists_generating_twoNode_preimages hm q hq hk
    (T.subtype (F.sylow_le_of_mem_Hz hI)) (B.subgroupOf I)
    (subgroupOf_mono I (show (T : Subgroup G) ≤ B from le_sup_right)) eB
  refine ⟨e,b,i,?_,hb,hBi,hPn,?_,?_,?_⟩
  · intro k
    exact congrArg eK (innerQuotientEquiv_on_component I K hn hgen hz hi k)
  · rw [←Subgroup.map_map,hPimage,Subgroup.map_map]
    exact hBi
  · intro j
    simpa only [map_subgroupOf_eq_of_le hBI] using map_mono (f := I.subtype) (hBpre j)
  · rw [←Subgroup.map_iSup,hall,←MonoidHom.range_eq_map,range_subtype]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Subgroup Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem solvable_of_pair_quotient {X : Type*} [Group X] [Finite X]
    (e : (X ⧸ pCore 2 X) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    Group.IsSolvable X := by
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  let : Group.IsSolvable (X ⧸ pCore 2 X) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 X) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 X)).mpr ⟨inferInstance,inferInstance⟩

/-- Original 14.7.29 applies to the actual product-row pullback. The
PSL₃(2) row is the only rank-two preimage that can escape M. -/
theorem local_inner_linear_exists_escaping_linearThree
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
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
    (structural G T) I K hI hn hgen hLK (by omega : 2 ≤ m) eK hi
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
  have hmodel : Nonempty (HStar (J j) ≃* Matrix.PSL3Two.PSL) := by
    rcases hrow with he | ⟨he⟩
    · exact he
    · exact (hj (solvable_point_overgroup_le_normalizer d h hab structural previous faithful earlier
        (J j) hJH hJB (solvable_of_pair_quotient he.some))).elim
  refine ⟨J j,?_,hJI,hJB,hmodel⟩
  refine ⟨⟨?_,fun _ hx => hJB (hx.elim mem_sup_left mem_sup_right)⟩,hJH,hj⟩
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hp : F.Vi 1 ≤ (J j).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsPGroup.of_card (p := 2) (n := 1) (by simpa using hc))
      ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans hJB))) hJH
  intro hz
  have hb := le_bot_iff.mp (hz ▸ hp)
  simp [hb] at hc

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Subgroup Theory.GroupTheory
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components
open BinaryLinear.OuterCyclic
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem binary_linear_model {Q : Type*} [Group Q] {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL Q n 2) : Nonempty (Q ≃* LinearGroup n) := by
  obtain ⟨E,_,_,hE,⟨a⟩⟩ := hm
  let := Fintype.ofFinite E
  let f : E ≃+* ZMod 2 := (ZMod.ringEquivOfPrime E Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hE)).symm
  exact ⟨a.trans ((Atlas.fieldEquivPSL n f).trans (projectiveEquivLinear hn))⟩

/-- Apply the quotient recovery and the constructed rank-two family to the
actual normal component selected in the original point normalizer. The
14.7.48 outputs are the sole new earlier-source input. No small-row
exclusion, parabolic generation or local-containment premise is supplied. -/
theorem original_exists_component_quotient_reduction
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
        ∀ (m : ℕ), (m = 3 ∨ m = 4) →
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) (m + 1) 2 →
          (∀ (t : G) (ht : t ∈ (T : Subgroup G)),
            (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
              MulAut.innerSubgroup (K ⧸ pCore 2 K)) →
          ∃ J : Subgroup G, J ∈ F.Hz L (normalizer (L : Set G)) ∧ J ≤ F.H ∧
            F.Li L 1 ⊔ (T : Subgroup G) ≤ J ∧
            Nonempty (HStar J ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨K,hKH,hK,hKn,hKM,hTK,_,hmodels,hunique⟩ :=
    original_exists_normal_component_reduction d h hab structural previous faithful earlier
  obtain ⟨hLK,hgen,hcomm⟩ := source48 K hKH hK
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  refine ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,?_,hTK,?_⟩
  · intro hmodel
    obtain ⟨eK⟩ := binary_linear_model (by decide : 0 < 3) hmodel
    exact linearThree_full_quotient_at h (structural G T) F.H K hH hKH hKn hgen
      (eK.trans (projectiveEquivLinear (by decide : 0 < 3)).symm)
  · intro m hm hmodel hi
    obtain ⟨eK⟩ := binary_linear_model (by omega : 0 < m + 1) hmodel
    exact local_inner_linear_exists_escaping_linearThree d h hab structural previous faithful earlier
      F.H K hH hTK hgen hLK hm eK hi

/-- Both small component rows and the inner linear rows now reduce to
actual full small quotients on the original selected component. The
14.7.11 contradiction is not included in the inputs or the conclusion. -/
theorem original_exists_component_quotient_reduction_with_six
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
      (Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) →
        Nonempty (HStar F.H ≃* alternatingGroup (Fin 6)) ∨
          Nonempty (HStar F.H ≃* Equiv.Perm (Fin 6))) ∧
      ∃ hn : (T : Subgroup G) ≤ normalizer (K : Set G),
        ∀ (m : ℕ), (m = 3 ∨ m = 4) →
          ClassicalGroup.IsPSL (K ⧸ pCore 2 K) (m + 1) 2 →
          (∀ (t : G) (ht : t ∈ (T : Subgroup G)),
            (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
              MulAut.innerSubgroup (K ⧸ pCore 2 K)) →
          ∃ J : Subgroup G, J ∈ F.Hz L (normalizer (L : Set G)) ∧ J ≤ F.H ∧
            F.Li L 1 ⊔ (T : Subgroup G) ≤ J ∧
            Nonempty (HStar J ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,hthree,hn,hinner⟩ :=
    original_exists_component_quotient_reduction d h hab structural previous faithful earlier source48
  refine ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,hthree,?_,hn,hinner⟩
  rintro ⟨eK⟩
  exact alternatingSix_full_quotient_at h (structural G T) F.H K
    (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) hKH hKn hgen eK

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
