module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.Setup
public import Theory.Representation.PSL3Two.SmallModuleProperties

/-!
# Ambient deductions in the local collapse

Unique maximal two-local containment kills C_Q(L) once K-centralization has
been proved. The nonsplit-extension displacement then contradicts the actual
H_z escape. Once Q=S, the original full natural action gives T≤L and the
characteristic center gives N_G(L)=L. Characteristic two and the original
natural Sylow fixed line supply the literal Ru center and centralizer.

There is also a short alternative to the last cardinality argument in
14.7.74: 14.7.73(2) now gives |H:K|=2. The original map H→S₅ has K-image A₅,
so its kernel O₂(H) lies in K. Relative normality identifies it with O₂(K).
This does not assume that equality when descending any preceding action.

The projective splitting and natural-extension premises below are still
separate proof obligations. These conditional reductions are not 14.7.74.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
printed p.1077 (PDF p.1094).
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
open Chapter12.Section08 CriticalFusion.Source ChapterJ
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (a : Prior d)
include a

/-- The unique maximal two-local over LT kills the literal fixed subgroup.
The K-centralization premise is the second Gaschütz/coprime-action step. -/
theorem QL_eq_bot_of_K_centralizes
    (hK : K F ≤ centralizer (QL T L : Set G)) : QL T L = ⊥ := by
  by_contra hne
  have hn : normalizer (QL T L : Set G) ≤ normalizer (L : Set G) := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G))
    · intro N hN hLN
      exact Set.mem_singleton_iff.mp (a.unique_overgroup ▸
        (show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
          from ⟨hN, hLN⟩))
    · exact (isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).to_le inf_le_left
    · exact hne
    · exact LT_normalizes_QL d a
  exact K_not_le_normalizer d a.sylow_normalizes
    ((hK.trans (Subgroup.centralizer_le_normalizer _)).trans hn)

/-- The full natural action absorbs T as soon as its kernel Q lies in L. -/
theorem T_le_L_of_Q_le_L (hQL : Q T L ≤ L) : (T : Subgroup G) ≤ L := by
  intro t ht
  have htV : t ∈ normalizer (V : Set G) := by
    simpa only [F.last] using F.invariant 3 ht
  obtain ⟨l, hl, he⟩ := d.natural.full_L_action (V.normalizerMonoidHom ⟨t, htV⟩)
  have hc : l⁻¹ * t ∈ centralizer (V : Set G) := by
    intro v hv
    have hh := congrArg (fun y : G => l⁻¹ * y * t) (he ⟨v, hv⟩)
    change l⁻¹ * (l * v * l⁻¹) * t = l⁻¹ * (t * v * t⁻¹) * t at hh
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  have hcQ : l⁻¹ * t ∈ Q T L := by
    rw [← a.centralizer_LT]
    exact ⟨(L ⊔ (T : Subgroup G)).mul_mem (mem_sup_left (L.inv_mem hl))
      (mem_sup_right ht), hc⟩
  have hh := L.mul_mem hl (hQL hcQ)
  simpa only [mul_inv_cancel_left] using hh

/-- The characteristic center of O₂(L), followed by 14.7.67(5), controls M. -/
theorem normalizer_L_eq_of_Q_eq_S (hQ : Q T L = S L F) :
    normalizer (L : Set G) = L := by
  have hTL := T_le_L_of_Q_le_L d a (hQ.le.trans (a.core.trans_le (pCoreIn_le 2 L)))
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rw [← a.center, a.core]
    exact (normalizer_le_normalizer_characteristic_image L (pCore 2 L)).trans
      (normalizer_le_normalizer_characteristic_image _ (Subgroup.center _))
  apply le_antisymm _ L.le_normalizer
  rw [← d.lemma_14_7_67_five a.separation, sup_eq_left.mpr hTL] at hMV
  exact hMV

/-- The natural action gives characteristic two on L without an extra certificate. -/
theorem L_characteristic_two :
    L ⊓ centralizer (L.pCoreIn 2 : Set G) ≤ L.pCoreIn 2 := by
  have hVS : V ≤ L.pCoreIn 2 := a.steinberg.kernel_le.trans_eq a.core
  exact (inf_le_inf_left L (centralizer_le hVS)).trans_eq d.natural.centralizer_L

/-- The actual Ru application discharges both T≤L and characteristic two. -/
theorem Ru_center_of_Q_eq_S (hQ : Q T L = S L F) :
    sylowCenter T = F.Vi 1 ∧ F.H = ChapterJ.centralizerOfSylowCenter T := by
  have hTL := T_le_L_of_Q_le_L d a (hQ.le.trans (a.core.trans_le (pCoreIn_le 2 L)))
  have hz := source_sylowCenter_eq_point d hTL (L_characteristic_two d a)
    (by rw [← a.core]; exact a.center)
  exact ⟨hz, source_H_eq_RuTwo_overgroup d hz⟩

/-- The same marked Steinberg section has the source order 2¹¹. -/
theorem card_S : Nat.card (S L F) = 2 ^ 11 := by
  have hv : Nat.card V = 2 ^ 3 := by simpa only [F.last] using F.card 3 (by decide)
  have hs : Nat.card BinaryLinearThree.Steinberg = 2 ^ 8 := by
    classical
    let : Finite BinaryLinearThree.Steinberg :=
      Finite.of_surjective (fun s => (a.steinberg.coordinates s).toAdd)
        (fun w => a.steinberg.onto (Multiplicative.ofAdd w))
    let := Fintype.ofFinite BinaryLinearThree.Steinberg
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2),
      BinaryLinearThree.finrank_steinberg, ZMod.card]
  rw [a.steinberg.card_section, hs, hv]
  norm_num

/-- Once T≤L, the earlier 14.7.73(2) index is precisely |H:K|=2. -/
theorem K_index_in_H (hTL : (T : Subgroup G) ≤ L) :
    ((K F).subgroupOf F.H).index = 2 := by
  let KH := (K F).subgroupOf F.H
  let TH := (T : Subgroup G).subgroupOf F.H
  let : KH.Normal := normal_subgroupOf_of_le_normalizer (H_normalizes_K F)
  have hsup : KH ⊔ TH = ⊤ := by
    rw [← subgroupOf_sup (K_le_H F) (F.invariant 1), ← d.residual_product, subgroupOf_self]
  have hi := a.sylow_index
  rw [inf_eq_left.mpr hTL, inf_relIndex_left] at hi
  calc
    KH.index = KH.relIndex (KH ⊔ TH) := by rw [hsup, relIndex_top_right]
    _ = KH.relIndex TH := relIndex_sup_left _ _
    _ = (K F).relIndex (T : Subgroup G) := relIndex_subgroupOf (F.invariant 1)
    _ = 2 := hi

/-- The index-two K and its actual alternating image force the star kernel
inside K. No equality between the two cores is used in this argument. -/
theorem QH_eq_P_of_T_le_L (hTL : (T : Subgroup G) ≤ L) :
    F.H.pCoreIn 2 = (K F).pCoreIn 2 := by
  let KH := (K F).subgroupOf F.H
  let AH := (alternatingGroup (Fin 5)).comap d.qH
  have hKA : KH ≤ AH := (map_le_iff_le_comap).mp d.K_image.le
  have hiA : AH.index = 2 := by
    rw [index_comap, MonoidHom.range_eq_top_of_surjective _ d.qH_surjective,
      relIndex_top_right, alternatingGroup.index_eq_two]
  have hiK : KH.index = 2 := K_index_in_H d a hTL
  have hm := relIndex_mul_index hKA
  rw [hiA, hiK] at hm
  have hAK : AH ≤ KH := relIndex_eq_one.mp (by omega : KH.relIndex AH = 1)
  have hker : d.qH.ker ≤ KH := by
    apply le_trans _ hAK
    intro x hx
    change d.qH x ∈ alternatingGroup (Fin 5)
    rw [MonoidHom.mem_ker.mp hx]
    exact one_mem _
  have hQK : F.H.pCoreIn 2 ≤ K F := by
    intro x hx
    have hh : (⟨x, pCoreIn_le 2 F.H hx⟩ : F.H) ∈ d.qH.ker := by
      rw [d.qH_ker]
      exact hx
    exact hker hh
  apply le_antisymm _ P_le_QH
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 F.H) hQK
    ((K_le_H F).trans (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))))

/-- All terminal conclusions, conditional only on the remaining Q=S collapse.
The original residual product H=KT is retained verbatim. -/
theorem conclusions_of_Q_eq_S (hQ : Q T L = S L F) :
    normalizer (L : Set G) = L ∧
    S L F = (normalizer (L : Set G)).pCoreIn 2 ∧
    F.H = K F ⊔ (T : Subgroup G) ∧
    F.H.pCoreIn 2 = (K F).pCoreIn 2 ∧
    sylowCenter T = F.Vi 1 ∧ F.H = ChapterJ.centralizerOfSylowCenter T := by
  have hm := normalizer_L_eq_of_Q_eq_S d a hQ
  have ht := T_le_L_of_Q_le_L d a (hQ.le.trans (a.core.trans_le (pCoreIn_le 2 L)))
  exact ⟨hm, by simpa only [hm] using a.core, d.residual_product,
    QH_eq_P_of_T_le_L d a ht, Ru_center_of_Q_eq_S d a hQ⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
