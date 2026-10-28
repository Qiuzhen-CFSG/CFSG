module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCubicSplit
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Section

/-!
# Excluding the doubled Thompson factor

The normal S₃ × S₃ alternative in the literal Thompson image forces every
two-perfect {2,3}-subgroup of the action quotient to be subnormal. Apply
this to the original point residual, using its lifted cubic supplement
to prove the order restriction and the original I₀ cover for the rank
bound. This contradicts the proved non-subnormality of L₁⁺.

The remaining solvable image is a single normal S₃. The nonsolvable
selection already supplies a normal A₅ or L₃(2). Thus the same Y, I₀,
point-span quotient and lifted point cubic admit a normal small factor,
with both faithful cubic projections and normalization by the original T.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1059,
refs/quasithin.pdf. The terminal projection contradiction is separate.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter14.Section04.LargerDimension.LocalAction.Components
open ChapterB.InternalThompsonAction Chapter7.NormalizedSource.DoubledBinaryThompson
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Exclude the doubled S₃ image using the original cover and select a
normal small factor. The non-subnormal actor is an actual subgroup of the
same action quotient, not a bound on its three-rank. -/
theorem reduced_thompson_normal_small_factor
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hTI : (T : Subgroup G) ≤ I)
    (hI : I ∈ Chapter1.H G) (hD : IsSQTK KnownSimple.IsKnownSimple I)
    (U : Subgroup I) [U.Normal] [IsElementaryAbelian 2 U]
    (hr : IsPReduced 2 U) (hne : thompsonImage U ≠ ⊥)
    (N : Subgroup (ActionQuotient U)) (hp : IsPPerfect 2 N)
    (ho : ∃ m n : ℕ, Nat.card N ∣ 2 ^ m * 3 ^ n) (hns : ¬ N.IsSubnormal) :
    ∃ A : Subgroup (ActionQuotient U), A ≤ thompsonImage U ∧ A.Normal ∧
      (Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨
        Nonempty (A ≃* alternatingGroup (Fin 5)) ∨
          Nonempty (A ≃* Matrix.PSL3Two.PSL)) := by
  classical
  by_cases hs : Group.IsSolvable (thompsonImage U)
  · let : (elementaryAbelianMaxJ (⊤ : Subgroup I)).Characteristic :=
      elementaryAbelianMaxJ_top_characteristic
    let : (thompsonImage U).Normal :=
      (inferInstance : (elementaryAbelianMaxJ (⊤ : Subgroup I)).Normal).map
        (actionMk U) (QuotientGroup.mk'_surjective _)
    rcases solvable_reduced_thompson_models U hD hr.quotient_pCore_eq_bot hne hs with he | he
    · exact ⟨thompsonImage U,le_rfl,inferInstance,Or.inl he⟩
    · obtain ⟨e⟩ := he
      exact (hns (NormalSymmetricThreePairRank.isSubnormal_of_twoPerfect_of_pair_cover
        (actionMk U) (QuotientGroup.mk'_surjective _)
        (hD.stronglyQuasithin 3 (by decide) (by decide)) (thompsonImage U) e N hp ho)).elim
  · obtain ⟨C,hCJ,_,_,hn,_,_,_,he⟩ :=
      nonsolvable_reduced_thompson_normal_factor T hE faithful I hTI hI hD U hr hs
    exact ⟨C.map (actionMk U),map_mono hCJ,
      hn.map _ (QuotientGroup.mk'_surjective _),Or.inr he⟩

open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Representation Representation.BinaryOffender Stellmacher
variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- In the same constructed local, the doubled S₃ alternative is impossible.
The selected small factor is normal, hence normalized by the original T;
the same point cubic retains its two faithful projections. -/
theorem local_nonnormal_component_weakClosure_normal_factor
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (star F c.Uα) = 2 ∧
      let P := F.Vi 1 ⊔ c.Zα
      let J := F.Li L 1 ⊔ (T : Subgroup G)
      let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
      let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
      let I₀ := J ⊔ Y
      let W₀ := ChapterE.indexedWeakClosure V R 0
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧ P ≤ F.U ⊓ c.Uα ∧
      R ≤ (T : Subgroup G) ∧ J ≤ normalizer (R : Set G) ∧
      R ≤ normalizer (P : Set G) ∧ Chapter1.IsSylowIn 2 R Y ∧
      Y ⊓ centralizer (P : Set G) = Y.pCoreIn 2 ∧
      Nonempty (Y ⧸ pCore 2 Y ≃* Equiv.Perm (Fin 3)) ∧
      V ≤ W₀ ∧ W₀ ≤ R ∧ I₀ ≤ normalizer (W₀ : Set G) ∧
      IsTwoLocal (normalizer (W₀ : Set G)) ∧ normalizer (W₀ : Set G) ≠ ⊤ ∧
      I₀ = J ⊔ c.Qα ∧ HasCharacteristicTwo I₀ ∧
      IsSQTK KnownSimple.IsKnownSimple I₀ ∧
      IsPReduced 2 ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀) ∧
      P ≤ conjugateSpanBy (F.Vi 1) I₀ ∧ conjugateSpanBy (F.Vi 1) I₀ ≤ W₀ ∧
      ⁅conjugateSpanBy (F.Vi 1) I₀,elementaryAbelianMaxJ (T : Subgroup G)⁆ ≠ ⊥ ∧
      letI : ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀).Normal :=
        normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
      let q := QuotientGroup.mk'
        (centralizer ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀ : Set I₀))
      (elementaryAbelianMaxJ (⊤ : Subgroup I₀)).map q ≠ ⊥ ∧
      ¬ (((F.Li L 1).subgroupOf I₀).map q).IsSubnormal ∧
        ((F.Li L 1).subgroupOf I₀).map q ≠ ⊥ ∧
        ¬ F.H.pCoreIn 2 ⊔ c.Qα ≤ normalizer (F.Li L 1 : Set G) ∧
        ¬ F.H.pCoreIn 2 ⊔ c.Qα ≤ normalizer (L : Set G) ∧
        Y ≤ normalizer ((pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
          (F.Li L 1 ⊓ centralizer (P : Set G)).subtype : Set G) ∧
        let RY := (pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
          (F.Li L 1 ⊓ centralizer (P : Set G)).subtype
        RY ⊔ (F.Li L 1).pCoreIn 2=F.Li L 1 ∧
          ∃ l : F.H, (l:G) ∈ RY ∧ orderOf (l:G)=3 ∧
            zpowers (l:G) ⊔ (F.Li L 1).pCoreIn 2=F.Li L 1 ∧
            ∃ y ∈ F.H.pCoreIn 2 ⊔ c.Qα, orderOf y = 3 ∧ Commute (l : G) y ∧
              IsElementaryAbelian 3 (zpowers y ⊔ zpowers (l : G) : Subgroup G) ∧
              Nat.card (zpowers y ⊔ zpowers (l : G) : Subgroup G) = 9 ∧
              Nat.card (((zpowers y ⊔ zpowers (l : G)).subgroupOf I₀).map q) = 9 ∧
              J ⊔ (zpowers y ⊔ zpowers (l : G)) = I₀ ∧
              ¬ ((zpowers y ⊔ zpowers (l : G)).subgroupOf I₀).map q ≤
                normalizer (((F.Li L 1).subgroupOf I₀).map q : Set _) ∧
              ∃ A : Subgroup _, A ≤ (elementaryAbelianMaxJ (⊤ : Subgroup I₀)).map q ∧
                (A.subgroupOf ((elementaryAbelianMaxJ (⊤ : Subgroup I₀)).map q)).Normal ∧
                A.IsSubnormal ∧ A.Normal ∧
                (Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨
                  A.Normal ∧ (Nonempty (A ≃* alternatingGroup (Fin 5)) ∨
                    Nonempty (A ≃* Matrix.PSL3Two.PSL))) ∧
                pResidual 2 (I₀ ⧸ centralizer
                  ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀ : Set I₀)) ≤ normalizer (A : Set _) ∧
                ((F.Li L 1).subgroupOf I₀).map q ≤ normalizer (A : Set _) ∧
                ((zpowers y ⊔ zpowers (l : G)).subgroupOf I₀).map q ≤
                  normalizer (A : Set _) ∧
                ((T : Subgroup G).subgroupOf I₀).map q ≤ normalizer (A : Set _) ∧
                ((T : Subgroup G).subgroupOf I₀).map q ≤
                  normalizer (((F.Li L 1).subgroupOf I₀).map q : Set _) ∧
                CubicFactorSplit (((zpowers y ⊔ zpowers (l : G)).subgroupOf I₀).map q) A
                  (((F.Li L 1).subgroupOf I₀).map q) (((zpowers (l : G)).subgroupOf I₀).map q) := by
  obtain ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hmove,hJplus,hsub,hne,hYn,hescape,hres,hgen,
    l,hl,hl3,hlgen,y,hy,hy3,hly,hE9,hcard,hplus,hIgen,hplusNot⟩ :=
    local_nonnormal_component_weakClosure_thompson d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
  let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
  let I₀ := J ⊔ Y
  let W := conjugateSpanBy (F.Vi 1) I₀
  let : (W.subgroupOf I₀).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let q := QuotientGroup.mk' (centralizer (W.subgroupOf I₀ : Set I₀))
  let E := zpowers y ⊔ zpowers (l : G)
  let Eplus := (E.subgroupOf I₀).map q
  let Bplus := ((zpowers (l : G)).subgroupOf I₀).map q
  let D := (F.Li L 1).subgroupOf I₀
  let Dplus := D.map q
  let : IsElementaryAbelian 3 E := hE9
  have hEI : E ≤ I₀ := le_sup_right.trans_eq hIgen
  let : IsElementaryAbelian 3 (E.subgroupOf I₀) := IsElementaryAbelian.subgroupOf hEI
  have hLI : F.Li L 1 ≤ I₀ := le_sup_left.trans le_sup_left
  have hpowL : zpowers (l : G) ≤ F.Li L 1 := le_sup_left.trans_eq hlgen
  have hlI : (l : G) ∈ I₀ := hLI (hpowL (mem_zpowers _))
  let lI : I₀ := ⟨l,hlI⟩
  have hpow : (zpowers (l : G)).subgroupOf I₀ = zpowers lI := by
    apply map_injective I₀.subtype_injective
    rw [map_subgroupOf_eq_of_le (hpowL.trans hLI),MonoidHom.map_zpowers]
    rfl
  have hgenD : zpowers lI ⊔ D.pCoreIn 2 = D := by
    rw [show D = (F.Li L 1).subgroupOf I₀ from rfl,
      pCoreIn_subgroupOf 2 _ I₀ hLI,←hpow,
      ←subgroupOf_sup (hpowL.trans hLI) ((pCoreIn_le 2 _).trans hLI),hlgen]
  have hpD : IsPPerfect 2 D :=
    (show IsPPerfect 2 (F.Li L 1) from isPPerfect_embedded_pResidual 2 _).of_surjective
      (subgroupOfEquivOfLe hLI).symm.toMonoidHom (subgroupOfEquivOfLe hLI).symm.surjective
  have hxE : zpowers lI ≤ E.subgroupOf I₀ := by
    rw [←hpow]
    exact comap_mono le_sup_right
  have hpDplus : IsPPerfect 2 Dplus := hpD.of_surjective (q.subgroupMap D)
    (q.subgroupMap_surjective D)
  have horder : ∃ m n : ℕ, Nat.card Dplus ∣ 2 ^ m * 3 ^ n := by
    obtain ⟨m,n,hmn⟩ := NormalSymmetricThreePairRank.two_three_order_of_cubic_supplement
      D lI ((I₀.orderOf_coe lI).symm.trans hl3) hgenD
    exact ⟨m,n,(card_map_dvd D q).trans hmn⟩
  let : IsElementaryAbelian 2 (W.subgroupOf I₀) := hred.elementary
  have hTI : (T : Subgroup G) ≤ I₀ := le_sup_right.trans le_sup_left
  have hWI : W ≤ I₀ := hVIW.trans (hWR.trans (hRT.trans hTI))
  have hHI : I₀ ∈ Chapter1.H G := by
    have hw : W ≤ I₀.pCoreIn 2 := by
      have hw₀ : W.subgroupOf I₀ ≤ pCore 2 I₀ := hred.le_pCore
      simpa only [pCoreIn,map_subgroupOf_eq_of_le hWI] using
        map_mono (f := I₀.subtype) hw₀
    intro hz
    have hzP : F.Vi 1 ⊔ c.Zα = ⊥ := bot_unique ((hPVI.trans hw).trans hz.le)
    rw [hzP,card_bot] at hfour
    norm_num at hfour
  obtain ⟨A,hAJ,hAnormal,hmodels⟩ := reduced_thompson_normal_small_factor T
    (d.qtke.evenCharacteristic T) faithful I₀ hTI hHI hsqtk
    (W.subgroupOf I₀) hred hJplus Dplus hpDplus horder hsub
  let : A.Normal := hAnormal
  have hmodel : Nonempty (A ≃* Equiv.Perm (Fin 3)) ∨
      A.Normal ∧ (Nonempty (A ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (A ≃* Matrix.PSL3Two.PSL)) := hmodels.imp id (fun hm => ⟨hAnormal,hm⟩)
  have hLA : Dplus ≤ normalizer (A : Set _) := le_normalizer_of_normal
  have hPA : Eplus ≤ normalizer (A : Set _) := le_normalizer_of_normal
  have hTL : ((T : Subgroup G).subgroupOf I₀).map q ≤ normalizer (Dplus : Set _) := by
    have hn : (T : Subgroup G).subgroupOf I₀ ≤ normalizer (D : Set I₀) := by
      rw [show D = (F.Li L 1).subgroupOf I₀ from rfl,←subgroupOf_normalizer_eq hLI]
      exact comap_mono (T_normalizes_L₁ h structural)
    exact (map_mono hn).trans (D.le_normalizer_map q)
  refine ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hmove,hJplus,hsub,hne,hYn,hescape,hres,hgen,
    l,hl,hl3,hlgen,y,hy,hy3,hly,hE9,hcard,hplus,hIgen,hplusNot,
    A,hAJ,inferInstance,hAnormal.isSubnormal,hAnormal,hmodel,le_normalizer_of_normal,
    hLA,hPA,le_normalizer_of_normal,hTL,?_⟩
  have ht := cubic_factor_split_of_lift q (QuotientGroup.mk'_surjective _)
    (hsqtk.stronglyQuasithin 3 (by decide) (by decide))
    (E.subgroupOf I₀) D lI ((I₀.orderOf_coe lI).symm.trans hl3) hxE hgenD hpD
    hne hplus A hLA hPA hplusNot hmodel
  simpa only [←hpow] using ht

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
