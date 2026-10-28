module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.Ambient

/-!
# The nonsplit fixed-preimage case contradicts H_z escape

The pointwise commutator calculation uses the actual O₂(K)≤O₂(H), the
original natural section U/V₁, and H=KT. The replacement of O₂(L₁) by SP
uses precisely the two-core identity in 14.7.73(1). Once the natural-extension
argument gives [QC,O₂(L₁)]=V, centralization by S removes S from the actor.
Then K normalizes [QCU,O₂(K)]=V, contrary to the genuine H_z membership.

The two remaining module arguments are explicit premises; this file does
not certify either projective splitting or the nonsplit extension theorem.
Source: Aschbacher--Smith 14.7.74, printed p.1077 (PDF p.1094),
combined manuscript of 1 March 2004.
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
open Chapter12.Section08 CriticalFusion.Source ChapterJ
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (a : Prior d)

omit [Finite G] in
private theorem normalizes_commutator {A B D : Subgroup G}
    (hA : D ≤ normalizer (A : Set G)) (hB : D ≤ normalizer (B : Set G)) :
    D ≤ normalizer (⁅A, B⁆ : Subgroup G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hA hg),
    mem_normalizer_iff_map_conj_eq.mp (hB hg)]

omit [Finite G] in
private theorem sup_commutator_le {A B E Z : Subgroup G}
    (hn : A ⊔ B ≤ normalizer (Z : Set G))
    (hA : ⁅A,E⁆ ≤ Z) (hB : ⁅B,E⁆ ≤ Z) : ⁅A ⊔ B,E⁆ ≤ Z := by
  have hle : A ⊔ B ≤ commutatorPreimage (A ⊔ B) E Z :=
    sup_le (le_commutatorPreimage le_sup_left hA) (le_commutatorPreimage le_sup_right hB)
  exact (commutator_mono hle le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hn)

include a in
/-- The surviving natural U/V₁ section gives [U,O₂(K)]≤V₁ directly. -/
theorem U_P_commutator_le_point : ⁅F.U, (K F).pCoreIn 2⁆ ≤ F.Vi 1 := by
  let s := source_natural_U_section d a.point_kernel
  rw [commutator_comm]
  apply commutator_le.mpr
  intro p hp u hu
  let pH : F.H := ⟨p, pCoreIn_le 2 F.H (P_le_QH hp)⟩
  let uU : F.U := ⟨u, hu⟩
  let c : F.U := ⟨p * u * p⁻¹,
    (mem_normalizer_iff.mp (s.normalized pH.property) u).mp hu⟩
  have hpq : d.qH pH = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [d.qH_ker]
    exact P_le_QH hp
  have hc : s.coordinates c = s.coordinates uU := by
    apply Multiplicative.toAdd.injective
    have hh := s.equivariant pH uU
    change (s.coordinates c).toAdd = _ at hh
    simpa only [MonoidHom.comp_apply, hpq, map_one, Module.End.one_apply] using hh
  have hh := (s.coordinates_eq_one_iff (c * uU⁻¹)).mp (by
    rw [map_mul, map_inv, hc, mul_inv_cancel])
  exact hh

include a in
/-- The correction to the source notation is used here: the actor is O₂(L₁). -/
theorem QC_P_commutator_eq_of_parabolic
    (hCS : QC T L V ≤ centralizer (S L F : Set G))
    (hdisp : ⁅QC T L V, (F.Li L 1).pCoreIn 2⁆ = V) :
    ⁅QC T L V, (K F).pCoreIn 2⁆ = V := by
  let C := ⁅QC T L V, (K F).pCoreIn 2⁆
  have hSK : S L F ≤ K F :=
    le_sup_left.trans (Chapter1.isSylowIn_iff.mp a.parabolic_sylow).2.1
  have hSN : S L F ≤ normalizer ((K F).pCoreIn 2 : Set G) :=
    (hSK.trans (K F).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hSC : S L F ≤ normalizer (C : Set G) := normalizes_commutator
    ((le_centralizer_iff.mp hCS).trans (Subgroup.centralizer_le_normalizer _)) hSN
  have hn : S L F ⊔ (K F).pCoreIn 2 ≤ normalizer (C : Set G) :=
    sup_le hSC (normalizer_commutator_ge_right _ _)
  have hbound : ⁅S L F ⊔ (K F).pCoreIn 2, QC T L V⁆ ≤ C :=
    sup_commutator_le hn
      (by rw [commutator_comm, commutator_eq_bot_iff_le_centralizer.mpr hCS]; exact bot_le)
      (by rw [commutator_comm])
  rw [a.parabolic_core] at hdisp
  apply le_antisymm ((commutator_mono le_rfl le_sup_right).trans_eq hdisp)
  exact hdisp.symm.le.trans ((commutator_comm _ _).le.trans hbound)

include d in
/-- The first Gaschütz commutator bound makes the original QCU K-invariant. -/
theorem K_normalizes_QCU (hKC : ⁅QC T L V, K F⁆ ≤ F.U) :
    K F ≤ normalizer ((QC T L V ⊔ F.U : Subgroup G) : Set G) := by
  have hKU : K F ≤ normalizer (F.U : Set G) :=
    (K_le_H F).trans d.conjugationSection.normalized
  have hKN : K F ≤ normalizer ((QC T L V ⊔ F.U : Subgroup G) : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk
    change QC T L V ⊔ F.U ≤ (QC T L V ⊔ F.U).comap (MulAut.conj k).toMonoidHom
    apply sup_le
    · intro x hx
      have hh : ⁅k,x⁆ ∈ F.U := by
        rw [commutator_comm] at hKC
        exact commutator_le.mp hKC k hk x hx
      have hm := (QC T L V ⊔ F.U).mul_mem (mem_sup_right hh) (mem_sup_left hx)
      change k * x * k⁻¹ ∈ QC T L V ⊔ F.U
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hm
    · intro x hx
      exact mem_sup_right ((mem_normalizer_iff.mp (hKU hk) x).mp hx)
  exact hKN

include a in
/-- Once Gaschütz gives [QC,K]≤U, normalization and the two actual conjugate
spans prove that QC centralizes S. -/
theorem QC_centralizes_S (hKC : ⁅QC T L V, K F⁆ ≤ F.U) :
    QC T L V ≤ centralizer (S L F : Set G) := by
  have hCU : QC T L V ⊔ F.U ≤ centralizer (V : Set G) := by
    apply sup_le
    · exact (commutatorPreimage_le _ _ _).trans
        (a.centralizer_LT.symm.le.trans inf_le_right)
    · let := d.abelian
      intro x hx v hv
      exact congrArg Subtype.val (mul_comm (⟨v, Data.V_le_U F hv⟩ : F.U) ⟨x, hx⟩)
  have hHN : F.H ≤ normalizer ((QC T L V ⊔ F.U : Subgroup G) : Set G) := by
    rw [d.residual_product]
    apply sup_le (K_normalizes_QCU d hKC)
    exact (le_inf (le_sup_right.trans (LT_normalizes_QC d a))
      ((F.invariant 1).trans d.conjugationSection.normalized)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hUC : F.U ≤ centralizer ((QC T L V ⊔ F.U : Subgroup G) : Set G) :=
    conjugateSpanBy_le (le_centralizer_iff.mp hCU)
      (hHN.trans (normalizer_le_normalizer_centralizer _))
  have hUS : F.U ≤ centralizer (QC T L V : Set G) :=
    hUC.trans (centralizer_le (show QC T L V ≤ QC T L V ⊔ F.U from le_sup_left))
  apply le_centralizer_iff.mpr
  exact conjugateSpanBy_le hUS ((le_sup_left.trans (LT_normalizes_QC d a)).trans
    (normalizer_le_normalizer_centralizer _))

include a in
/-- The normalizer contradiction excludes the nonzero nonsplit extension. -/
theorem false_of_QC_parabolic_displacement
    (hKC : ⁅QC T L V, K F⁆ ≤ F.U)
    (hCS : QC T L V ≤ centralizer (S L F : Set G))
    (hdisp : ⁅QC T L V, (F.Li L 1).pCoreIn 2⁆ = V) : False := by
  have hCP := QC_P_commutator_eq_of_parabolic d a hCS hdisp
  have hCV : QC T L V ≤ normalizer (V : Set G) :=
    (commutatorPreimage_le _ _ _).trans (Q_normalizes_V (F := F))
  have hUC : F.U ≤ centralizer (V : Set G) := by
    let := d.abelian
    intro x hx v hv
    exact congrArg Subtype.val (mul_comm (⟨v, Data.V_le_U F hv⟩ : F.U) ⟨x, hx⟩)
  have hgen : ⁅QC T L V ⊔ F.U, (K F).pCoreIn 2⁆ = V := by
    apply le_antisymm
    · exact sup_commutator_le (sup_le hCV (hUC.trans (Subgroup.centralizer_le_normalizer _)))
        hCP.le ((U_P_commutator_le_point d a).trans (F.le_seed 1))
    · exact hCP.symm.le.trans (commutator_mono le_sup_left le_rfl)
  have hKN := K_normalizes_QCU d hKC
  have hKP : K F ≤ normalizer ((K F).pCoreIn 2 : Set G) :=
    (K F).le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hKV : K F ≤ normalizer (V : Set G) := by
    simpa only [hgen] using normalizes_commutator hKN hKP
  have hHV : F.H ≤ normalizer (V : Set G) := by
    rw [d.residual_product]
    exact sup_le hKV (by simpa only [F.last] using F.invariant 3)
  have hVL : normalizer (V : Set G) ≤ normalizer (L : Set G) := by
    rw [← d.lemma_14_7_67_five a.separation]
    exact sup_le L.le_normalizer a.sylow_normalizes
  exact H_not_le_normalizer d (hHV.trans hVL)

include a in
/-- Assembly of the fixed-preimage collapse, with both missing module arguments
visible. Their producers, not this conditional theorem, must discharge them. -/
theorem Q_eq_S_of_extension_inputs
    (hsplit : Q T L = QC T L V ⊔ S L F)
    (hKC : ⁅QC T L V, K F⁆ ≤ F.U)
    (hdisp : V < QC T L V → ⁅QC T L V, (F.Li L 1).pCoreIn 2⁆ = V) :
    Q T L = S L F := by
  have hVQ : V ≤ Q T L := a.steinberg.kernel_le.trans
    (a.core.le.trans (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer a.sylow_normalizes)))
  have hVC : V ≤ QC T L V := le_commutatorPreimage hVQ
    (le_normalizer_iff_commutator_le_left.mp d.natural.chosen.normalizes)
  have hCV : QC T L V = V := by
    by_contra hne
    exact false_of_QC_parabolic_displacement d a hKC (QC_centralizes_S d a hKC)
      (hdisp (lt_of_le_of_ne hVC (Ne.symm hne)))
  rw [hsplit, hCV, sup_eq_right.mpr a.steinberg.kernel_le]

include a in
/-- The fixed-preimage argument feeds the actual terminal and Ru conclusions. -/
theorem conclusions_of_extension_inputs
    (hsplit : Q T L = QC T L V ⊔ S L F)
    (hKC : ⁅QC T L V, K F⁆ ≤ F.U)
    (hdisp : V < QC T L V → ⁅QC T L V, (F.Li L 1).pCoreIn 2⁆ = V) :
    normalizer (L : Set G) = L ∧
    S L F = (normalizer (L : Set G)).pCoreIn 2 ∧
    F.H = K F ⊔ (T : Subgroup G) ∧
    F.H.pCoreIn 2 = (K F).pCoreIn 2 ∧
    sylowCenter T = F.Vi 1 ∧ F.H = ChapterJ.centralizerOfSylowCenter T :=
  conclusions_of_Q_eq_S d a (Q_eq_S_of_extension_inputs d a hsplit hKC hdisp)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse
