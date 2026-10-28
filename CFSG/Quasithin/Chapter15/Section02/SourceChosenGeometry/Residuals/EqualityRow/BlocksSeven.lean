module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.BlocksRankOne
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockModels.AlternatingSeven
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenNormalAction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddConjugation
public import Theory.GroupTheory.PGroup.NormalSupplementCore

/-!
# The actual A₇ chi-block exclusion in the equality row

The original wreath residual lies in O^{3'}(I), which is the actual normal
A₇ block. Its cubic rank forces QI to act by even permutations on the
whole block module. The marked kernel and the original Sylow group put
O₂(XQI) inside QI. The odd-core offender theorem then puts J(QI) in that
core, contradicting Thompson-normalizer control and equality-row escape.
Every action and subgroup map is the original one.

Source: Aschbacher--Smith, preliminary 15.2.23, printed p.1115,
refs/quasithin.pdf. No partner residual identity is assumed.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
open Section01 Section03 ChapterA.Section04 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (r : ResidualInput hsource H B)
include r

/-- The literal source residual belongs to the actual A₇ block. -/
theorem a7_block_contains_residual (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 7) :
    (pResidual 2 H).map H.subtype ≤ X.map I.subtype := by
  rw [←PlaneUniquenessPreceding.a7_block_eq_threeResidual (hsource := hsource) hI hX hb]
  exact r.residual_le_threeResidual hI

theorem a7_block_action_even (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 7) :
    ∃ hn : X.Normal, letI := hn
      ∃ q : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7),
      ∃ E : ChapterC.blockU X ≃* Multiplicative (BinaryPermutation.core (Fin 7)),
      ∃ f : I →* Equiv.Perm (Fin 7),
        (∀ x : X, f x = (q (QuotientGroup.mk' (pCore 2 X) x)).val) ∧
        (∀ g u, (E (MulAut.characteristic (ChapterC.blockU X) (MulAut.conjNormal g) u)).toAdd =
          BinaryPermutation.coreRepresentation (Fin 7) (f g) (E u).toAdd) ∧
        X.map f = alternatingGroup (Fin 7) ∧
        (f.comp X.subtype).ker = pCore 2 X ∧
        ((planeParabolicCore T H (⁅V,B⁆ : Subgroup G)).subgroupOf I).map f ≤ alternatingGroup (Fin 7) := by
  have hs := (Chapter3.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
  let hn : X.Normal := ChapterC.LocalC129.alternating_seven_normal hs hX hb
  let := hn
  obtain ⟨q,E,f,hf,hE,himage,hker⟩ := hb.seven_normal_action X
  refine ⟨hn,q,E,f,hf,hE,himage,hker,?_⟩
  let K := (pResidual 2 H).map H.subtype
  let K' := K.subgroupOf I
  let Q := planeParabolicCore T H (⁅V,B⁆ : Subgroup G)
  have hPI := (r.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right
  have hKI : K ≤ I := le_sup_left.trans hPI
  have hQI : Q ≤ I := (pCoreIn_le 2 _).trans hPI
  have hKX : K' ≤ X := by
    intro x hx
    obtain ⟨y,hy,he⟩ := r.a7_block_contains_residual hI hX hb hx
    exact (Subtype.ext he : y = x) ▸ hy
  let e : (pResidual 2 H) ≃* K' :=
    ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).trans
      (subgroupOfEquivOfLe hKI).symm
  have hr : 2 ≤ primeRank 3 K' := by
    rw [←primeRank_congr 3 e]
    exact r.residual_threeRank_ge_two
  have hnQ : K' ≤ normalizer (Q.subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq hQI]
    intro x hx
    exact r.planeParabolicCore_normalized hI (map_subtype_le (pResidual 2 H) hx)
  exact ChapterC.seven_normalized_two_image_even hKX hr
    (isPGroup_pCoreIn 2 _).comap_subtype hnQ f hker

theorem a7_extension_core_le (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 7) :
    (X.map I.subtype ⊔ planeParabolicCore T H (⁅V,B⁆ : Subgroup G)).pCoreIn 2 ≤ planeParabolicCore T H (⁅V,B⁆ : Subgroup G) := by
  obtain ⟨hn,_q,E,f,_hf,hE,_himage,hker,_heven⟩ := r.a7_block_action_even hI hX hb
  let := hn
  have hC := ChapterC.seven_action_kernel X E f hE
  let Y := X.map I.subtype
  let Q := planeParabolicCore T H (⁅V,B⁆ : Subgroup G)
  let R := (Y ⊔ Q).pCoreIn 2
  let R' := R.subgroupOf I
  let K := (pResidual 2 H).map H.subtype
  let K' := K.subgroupOf I
  let S := planeSylow T (⁅V,B⁆ : Subgroup G)
  let S' := S.subgroupOf I
  have hPI := (r.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right
  have hKI : K ≤ I := le_sup_left.trans hPI
  have hSI : S ≤ I := le_sup_right.trans hPI
  have hQI : Q ≤ I := (pCoreIn_le 2 _).trans hPI
  have hYI : Y ≤ I := map_subtype_le _
  have hRI : R ≤ I := (pCoreIn_le 2 _).trans (sup_le hYI hQI)
  have hIY : I ≤ normalizer (Y : Set G) := by
    have hh := X.le_normalizer_map I.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hRS : R ≤ S := r.plane_span_extension_core_le_sylow hI hYI hIY
  have hXR : X ≤ normalizer (R' : Set I) := by
    rw [←subgroupOf_normalizer_eq hRI]
    intro x hx
    exact (le_sup_left : Y ≤ Y ⊔ Q).trans
      ((Y ⊔ Q).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (Y ⊔ Q) (pCore 2 (Y ⊔ Q : Subgroup G))))
      (mem_map_of_mem I.subtype hx)
  have hRK : R' ≤ f.ker := by
    rw [hC]
    exact hb.2.1.normalizing_twoGroup_centralizes_blockU
      (isPGroup_pCoreIn 2 _).comap_subtype hXR le_normalizer_of_normal
  have hKX : K' ≤ X := by
    intro x hx
    obtain ⟨y,hy,he⟩ := r.a7_block_contains_residual hI hX hb hx
    exact (Subtype.ext he : y = x) ▸ hy
  have hk : IsPGroup 2 (f.comp K'.subtype).ker := by
    let j : (f.comp K'.subtype).ker →* pCore 2 X :=
      ((inclusion hKX).comp (f.comp K'.subtype).ker.subtype).codRestrict _ (by
        intro x
        rw [←hker]
        exact x.property)
    apply pCore_isPGroup.of_injective j
    intro x y hxy
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : pCore 2 X => ((z : X) : I)) hxy))
  have hSK : S' ≤ normalizer (K' : Set I) := by
    rw [←subgroupOf_normalizer_eq hKI]
    intro s hs
    exact (inf_le_left.trans r.geometry.outside.1.1.2).trans
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))) hs
  have hSp : IsPGroup 2 S' :=
    (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
  have hle : R' ≤ (K' ⊔ S').pCoreIn 2 :=
    (le_inf (fun x hx => (le_sup_right : S' ≤ K' ⊔ S') (hRS hx)) hRK).trans
      (inf_ker_le_core_of_two_supplement f K' S' hSK hSp hk)
  have hm := map_mono (f := I.subtype) hle
  rw [map_subgroupOf_eq_of_le hRI,map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
    Subgroup.map_sup,map_subgroupOf_eq_of_le hKI,map_subgroupOf_eq_of_le hSI] at hm
  exact hm


theorem a7_block_false_of_eq
    (he : partnerSpan H Mc = residual H)
    (hI : PlaneEscapes Mc (⁅V,B⁆ : Subgroup G) I) (_hfit : generalizedFitting I = pCore 2 I)
    {X : Subgroup I} (hX : ChapterC.IsBlock X)
    (hb : ChapterC.IsAlternatingBlock X 7) : False := by
  obtain ⟨hn,_q,E,f,_hf,hE,_himage,hker,heven⟩ := r.a7_block_action_even hI hX hb
  let := hn
  let W := (ChapterC.blockU X).map X.subtype
  let : W.Normal := inferInstance
  let : IsElementaryAbelian 2 (ChapterC.blockU X) := hb.2.1.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map X.subtype
  let j : ChapterC.blockU X ≃* W :=
    (ChapterC.blockU X).equivMapOfInjective X.subtype X.subtype_injective
  let F : W ≃* Multiplicative (BinaryPermutation.core (Fin 7)) := j.symm.trans E
  have hF (g : I) (w : W) : (F (MulAut.conjNormal g w)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 7) (f g) (F w).toAdd := by
    have hh : j.symm (MulAut.conjNormal g w) =
        MulAut.characteristic (ChapterC.blockU X) (MulAut.conjNormal g) (j.symm w) := by
      apply j.injective
      rw [j.apply_symm_apply]
      apply Subtype.ext
      change g * (w : I) * g⁻¹ = g * (((j.symm w : ChapterC.blockU X) : X) : I) * g⁻¹
      congr 2
      exact (congrArg Subtype.val (j.apply_symm_apply w)).symm
    change (E (j.symm _)).toAdd = _
    rw [hh]
    exact hE g (j.symm w)
  let Q := planeParabolicCore T H (⁅V,B⁆ : Subgroup G)
  let Q' := Q.subgroupOf I
  have hPI := (r.residual_sup_planeSylow_le_for_blocks hI).trans inf_le_right
  have hQI : Q ≤ I := (pCoreIn_le 2 _).trans hPI
  have hQcore : I.pCoreIn 2 ≤ Q := r.escape_core_le_planeParabolicCore hI
  have hWQ : W ≤ Q' := by
    intro w hw
    have hWcore := (map_mono (f := X.subtype) (ChapterC.blockU_le_core (L := X))).trans
      (pCoreIn_le_of_subnormal 2 hX.subnormal)
    exact hQcore (mem_map_of_mem I.subtype (hWcore hw))
  have hJ := ChapterB.Offenders.thompson_le_kernel_of_even_core_action (Or.inr rfl) W Q' hWQ f
    (ChapterC.seven_action_kernel X E f hE) F hF heven
  have hXP : Q' ≤ normalizer (X : Set I) := le_normalizer_of_normal
  have hk : IsPGroup 2 (f.comp X.subtype).ker := by
    rw [hker]
    exact pCore_isPGroup
  have hJcore : elementaryAbelianMaxJ Q' ≤ (X ⊔ Q').pCoreIn 2 :=
    (le_inf ((sSup_le fun _ hA => hA.1).trans le_sup_right) hJ).trans
      (inf_ker_le_core_of_two_supplement f X Q' hXP (isPGroup_pCoreIn 2 _).comap_subtype hk)
  have hm := map_mono (f := I.subtype) hJcore
  rw [←elementaryAbelianMaxJ_map_injective I.subtype I.subtype_injective,
    map_subgroupOf_eq_of_le hQI,map_pCoreIn_of_injective 2 _ I.subtype I.subtype_injective,
    Subgroup.map_sup,map_subgroupOf_eq_of_le hQI] at hm
  exact r.planeParabolicCore_thompson_not_le_core hI
    (r.alternating_block_not_le_partner_of_eq he (Or.inr rfl) hb)
    (r.a7_extension_core_le hI hX hb) hm

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry.ResidualInput
