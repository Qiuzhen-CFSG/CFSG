module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerG2Pair
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.NormalizedTwoGroups
public import Theory.GroupTheory.CentralizerSupplementDetector
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# The fixed-space detector at the original G₂ endpoint

Write U=U(L), Q=O₂(LT), R=O₂(XT), where X=O²(C_L(Ω₁Z(T))).
The factorization Q=U C_Q(Uᵈ) transfers a fixed-space detector from U to Q.
Mapping C_T(U)=Q by the original Sylow-normalizing conjugator puts
C_Q(Uᵈ) inside Qᵈ. Elementarity of Q then permits replacing Uᵈ by Qᵈ.
Restriction to R supplies the literal detector needed by the full maximum
elementary family contradiction. No later T-normal family is used.

The intrinsic model detector and common-image clauses remain with their
producers; no natural module marking is identified with the chosen module.
Source: Aschbacher--Smith 3.3.28, printed p.601, and B.2.21, pp.82--83.
Right conjugation by d is map by MulAut.conj d⁻¹.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The intrinsic-layer detector transfers to the actual elementary local core. -/
theorem g2Two_local_core_fixed_detector_of_factorization
    (D : ChosenModule T L V) (hb : ChapterC.IsG2TwoBlock L)
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hQe : IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2))
    (hfactor : (L ⊔ (T : Subgroup G)).pCoreIn 2 = (ChapterC.blockU L).map L.subtype ⊔
      ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer
        (((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom : Set G)))
    (a : G)
    (ha : a ∈ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom)
    (hfix : (ChapterC.blockU L).map L.subtype ⊓ centralizer
        (((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom : Set G) =
      (ChapterC.blockU L).map L.subtype ⊓ centralizer ({a} : Set G)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer
        (((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj d⁻¹).toMonoidHom : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer ({a} : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let U := (ChapterC.blockU L).map L.subtype
  let e := MulAut.conj d⁻¹
  let B := U.map e.toMonoidHom
  let W := Q.map e.toMonoidHom
  let : IsElementaryAbelian 2 Q := hQe
  let : IsElementaryAbelian 2 W := hQe.map e.toMonoidHom
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Q, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hQU : Q ≤ normalizer (U : Set G) := hQT.trans
    (D.sylow_normalizes_component.trans
      (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L)))
  have hUQ : U ≤ Q := by
    change U ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [hfactor]
    exact le_sup_left
  have hBW : B ≤ W := map_mono hUQ
  have hTmap : (T : Subgroup G).map e.toMonoidHom = (T : Subgroup G) :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (T : Set G)).inv_mem hd)
  have hm := congrArg (fun K : Subgroup G => K.map e.toMonoidHom)
    (hb.short.sylow_centralizer_blockU_eq_pCoreIn D.sylow_normalizes_component)
  rw [map_inf _ _ _ e.injective, hTmap, map_centralizer_equiv] at hm
  have hm' : (T : Subgroup G) ⊓ centralizer (B : Set G) = W := hm
  have hcover : Q ⊓ centralizer (B : Set G) ≤ W :=
    (inf_le_inf_right _ hQT).trans hm'.le
  exact (inf_centralizer_eq_of_commutative_cover Q B W hBW hcover).trans
    (inf_centralizer_singleton_of_centralizing_supplement Q U B hQU hfactor a ha hfix)

/-- The model detector and common-image theorem feed the original 3.3.28
contradiction on the full maximum elementary family of the literal R. -/
theorem false_of_g2_local_intrinsic_detector
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥) (hb : ChapterC.IsG2TwoBlock L)
    (B : Subgroup G) (hBN : B ≤ normalizer (T : Set G)) (hodd : Odd (Nat.card B))
    (d : G) (hd : d ∈ B) (hout : d ∉ normalizer (L : Set G))
    (hQe : IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2))
    (hfactor : (L ⊔ (T : Subgroup G)).pCoreIn 2 = (ChapterC.blockU L).map L.subtype ⊔
      ((L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer
        (((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom : Set G)))
    {H : Type v} [Group H] (q : blockLocalCore T L →* H)
    (hker : q.ker = ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (blockLocalCore T L))
    (a : G)
    (ha : a ∈ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom)
    (hfix : (ChapterC.blockU L).map L.subtype ⊓ centralizer
        (((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom : Set G) =
      (ChapterC.blockU L).map L.subtype ⊓ centralizer ({a} : Set G))
    (hcommon : ∀ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup (blockLocalCore T L)),
      ¬ A ≤ ((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf (blockLocalCore T L) →
        A.map q = ((((L ⊔ (T : Subgroup G)).pCoreIn 2).map
          (MulAut.conj d⁻¹).toMonoidHom).subgroupOf (blockLocalCore T L)).map q) : False := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let R := blockLocalCore T L
  let U := (ChapterC.blockU L).map L.subtype
  let e := MulAut.conj d⁻¹
  let W := Q.map e.toMonoidHom
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Q, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hHN : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hXL : blockLocalResidual T L ≤ L := (map_subtype_le _).trans inf_le_left
  have hQR : Q ≤ R := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
    (hQT.trans le_sup_right) ((sup_le (hXL.trans le_sup_left) le_sup_right).trans hHN)
  have hRmap : R.map e.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp
    (((blockLocalInvariance_of_g2Two h D hfixed hb).1 (Or.inr hb)).2
      ((normalizer (T : Set G)).inv_mem (hBN hd)))
  have hWR : W ≤ R := (map_mono hQR).trans hRmap.le
  have hUQ : U ≤ Q := by
    change U ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [hfactor]
    exact le_sup_left
  have haW : a ∈ W := (map_mono hUQ) ha
  let aR : R := ⟨a,hWR haW⟩
  have hfixQ := g2Two_local_core_fixed_detector_of_factorization D hb (hBN hd)
    hQe hfactor a ha hfix
  have hfixR := subgroupOf_inf_centralizer_singleton_of_eq Q W R hWR aR hfixQ
  exact false_of_g2_local_unique_image h D hfixed hb B hBN hodd d hd hout hQR hQe
    q hker aR haW hfixR hcommon

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
