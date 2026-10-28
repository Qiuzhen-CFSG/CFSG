module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCubicSplitting
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCubicRadicalSource

/-!
# The splitting on the original minimal five-core witness

Apply the full-module splitting to the same minimal I and its original
normal two-perfect lift. Its actual five-core quotient, full two-core
kernel, generation of I and escape from M are retained. The fixed eight
and moved complement are both I-invariant, the fixed eight meets V in
V₁, and it differs from V by original normalizer uniqueness.

No new action or local-recognition assumption is introduced. The result
does not exclude the simultaneous-cubic configuration; five-core
vanishing and the later reductions through 14.7.52 remain open.
Source: Aschbacher–Smith, 14.7.6, printed pp.1044–1045,
refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Representation
open Chapter12.Section08 CriticalFusion.Source
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- On any fixed original minimal five-core witness, the same two-perfect
lift has its exact two-core as full-module action kernel. Its fixed eight
and moved complement, and the full radical, are literal ambient subgroups. -/
theorem local_minimal_five_split_lift
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hne : pCore 5 (HStar I) ≠ ⊥)
    (hmin : ∀ E : Subgroup G, E ∈ F.Hz L (normalizer (L : Set G)) → E < I →
      pCore 5 (HStar E) = ⊥) :
    ∃ Y : Subgroup I,
      Y.Normal ∧ IsPPerfect 2 Y ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = pCore 5 (HStar I) ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      Nonempty ((Y ⧸ pCore 2 Y) ≃* pCore 5 (HStar I)) ∧
      ¬ Y.map I.subtype ≤ normalizer (L : Set G) ∧
      I = Y.map I.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH I),
        let := hU
        ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
          (((F.UH I).normalizerMonoidHom.comp (inclusion a.normalizes)).comp Y.subtype).ker =
            pCore 2 Y ∧
          let W := ⁅F.UH I,Y.map I.subtype⁆
          let C := F.UH I ⊓ centralizer (Y.map I.subtype : Set G)
          I ≤ normalizer (W : Set G) ∧ I ≤ normalizer (C : Set G) ∧
          W ⊔ C = F.UH I ∧ W ⊓ C = ⊥ ∧
          V ⊔ W = F.UH I ∧ V ⊓ W = ⊥ ∧ Nat.card C = 8 ∧
          V ⊓ C = F.Vi 1 ∧ C ≠ V ∧
          W ⊔ F.Vi 1 = F.UH I ⊓ centralizer (I.pCoreIn 2 : Set G) := by
  obtain ⟨I',Y,hI'I,hI',hne',_,hYn,hYp,hYm,hYk,he,hout,hgen,hs,hn,hU,
      hmove,hsup,hinter,hindices⟩ :=
    local_minimal_five_radical_reduction h hab structural previous faithful I hI hne
  have heq : I' = I := by
    by_contra hh
    exact hne' (hmin I' hI' (lt_of_le_of_ne hI'I hh))
  subst I'
  let := hU
  let := hYn
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  obtain ⟨_,a,_⟩ := Chapter12.Section09.NaturalSource.abelian_local_quadratic_actor h
    ⟨structural,uniqueness,previous⟩ F hab I hI
  let hf := local_f9_hypothesis h hab structural previous I hI
  let : IsElementaryAbelian 2
      (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU
  have hZ : F.Vi 1 ≤ centralizer (I : Set G) := le_centralizer_iff.mp hf.H_centralizes
  have hz := hZ.trans (centralizer_le (map_subtype_le Y))
  have hq : ⁅I.pCoreIn 2,F.UH I⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact hf.commutator_UH_QH_le_point
  have hY5 : IsPGroup 5 (Y ⧸ pCore 2 Y) := pCore_isPGroup.of_equiv he.some.symm
  have hk := local_radical_lift_action_kernel a Y hYp hY5 hYk hz hq hmove
  obtain ⟨hsplit,hdis⟩ := local_radical_lift_splitting a Y hYp hY5 hYk hz hq hmove
  have heigt := local_radical_fixed_eight h I Y hgen hz hmove hinter hsplit hdis
  have hrad := local_radical_eq_moved_sup_point h I Y hgen hz hmove hinter hdis hindices.1
  have hIB : I ≤ normalizer (Y.map I.subtype : Set G) := by
    have hh := Y.le_normalizer_map I.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hIW : I ≤ normalizer ((⁅F.UH I,Y.map I.subtype⁆ : Subgroup G) : Set G) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (a.normalizes hx),
      mem_normalizer_iff_map_conj_eq.mp (hIB hx)]
  have hIC := le_normalizer_inf a.normalizes
    (hIB.trans (normalizer_le_normalizer_centralizer _))
  let C := F.UH I ⊓ centralizer (Y.map I.subtype : Set G)
  have hCV : C ≠ V := by
    intro heq
    have hIV : I ≤ normalizer (V : Set G) := heq ▸ hIC
    exact hI.2.2 (hIV.trans (h.seed_normalizer_le structural uniqueness))
  have hVC : V ⊓ C = F.Vi 1 := by
    let := h.chosen.elementary
    let := F.localKernel_tilde_seed_elementary
    have hZC : F.Vi 1 ≤ C := le_inf a.kernel_le hz
    have hLN : F.Li L 1 ≤ normalizer ((V ⊓ C : Subgroup G) : Set G) :=
      le_normalizer_inf ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
        ((F.Li_one_le_of_mem_Hz hI).trans hIC)
    rcases F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide : 3 ≤ 3)
      (V ⊓ C) (le_inf (F.le_seed 1) hZC) inf_le_left hLN with heq | heq
    · exact heq
    · exfalso
      apply hCV
      symm
      apply eq_of_le_of_card_ge (heq.ge.trans inf_le_right)
      have hv : Nat.card V = 8 := by
        simpa only [F.last,show (2 : ℕ)^3 = 8 from rfl] using F.card 3 (by decide)
      exact heigt.2.le.trans hv.ge
  exact ⟨Y,hYn,hYp,hYm,hYk,he,hout,hgen,hU,a,hk,hIW,hIC,hsplit,hdis,
    local_span_eq_seed_sup_moved h I Y hgen,heigt.1,heigt.2,hVC,hCV,hrad⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
