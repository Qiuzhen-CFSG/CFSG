module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleCubicAction
public import Theory.GroupTheory.PResidual.OddConjugateSpan
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The original cubic conjugate span and its normalizer

The selected cubic centralizes the actual L/O₂(L) quotient. Its Sylow
conjugate span retains that commutator bound. It is two-perfect, so the
normalizing two-group error O₂(L) can be removed: L normalizes the span.

The span is a nontrivial normal subgroup of the solvable cubic Sylow join.
The original Borel join's nontrivial normal two-core makes this Sylow join
characteristic two; hence the span itself has nontrivial two-core.
Uniqueness over LT then bounds its full normalizer by N_G(L).

This proves the span-normalizer step of Aschbacher--Smith 13.2.7,
printed p.884, directly from the existing LT uniqueness theorem. The
selected component's normalization of this same span, and the final
outside contradiction, remain to be established.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The original component normalizes the literal Sylow-conjugate span of
its selected cubic lift; no change of lift or residual is made. -/
theorem single_cubic_span_normalized
    (c : SingleQuotientProduct T L H)
    (hYM : c.cubic_lift.map (H ⊔ borelResidual T L).subtype ≤ normalizer (L : Set G))
    (ha : ∀ (y : G) (hy : y ∈ c.cubic_lift.map (H ⊔ borelResidual T L).subtype),
      d.quotientNormalizerAction ⟨y,hYM hy⟩ = 1) :
    L ⊔ (T : Subgroup G) ≤ normalizer
      (conjugateSpanBy (c.cubic_lift.map (H ⊔ borelResidual T L).subtype)
        (T : Subgroup G) : Set G) := by
  let Y := c.cubic_lift.map (H ⊔ borelResidual T L).subtype
  let E := conjugateSpanBy Y (T : Subgroup G)
  let M := normalizer (L : Set G)
  let Q := L.pCoreIn 2
  have hMQ : M ≤ normalizer (Q : Set G) :=
    normalizer_le_normalizer_characteristic_image L (pCore 2 L)
  have hYP : Y ≤ commutatorPreimage M L Q := le_commutatorPreimage hYM
    (by rw [commutator_comm]; exact single_cubic_commutator_le_core d c hYM ha)
  have hEP : E ≤ commutatorPreimage M L Q := conjugateSpanBy_le hYP
    (commutatorPreimage_normalized M L Q (T : Subgroup G) hMQ
      (d.normalizes_L.trans M.le_normalizer) d.normalizes_L (d.normalizes_L.trans hMQ))
  have hEL : ⁅L,E⁆ ≤ Q := by
    rw [commutator_comm]
    exact (commutator_mono hEP le_rfl).trans (commutator_commutatorPreimage_le M L Q hMQ)
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer d.normalizes_L)).trans
      ((d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left)
  have hcY : Nat.card Y = 3 :=
    (card_map_of_injective (H ⊔ borelResidual T L).subtype_injective).trans c.cubic_card
  have hEp : IsPPerfect 2 E := isPPerfect_conjugateSpanBy_of_coprime Y (T : Subgroup G)
    (by rw [hcY]; decide)
  exact sup_le (le_normalizer_of_isPPerfect_of_commutator_le E L Q hEp
    (isPGroup_pCoreIn 2 L) (hQT.trans (le_normalizer_conjugateSpanBy Y (T : Subgroup G))) hEL)
      (le_normalizer_conjugateSpanBy Y (T : Subgroup G))
/-- The literal cubic conjugate span has its full normalizer in N_G(L).
Its nontrivial two-core is obtained inside the actual solvable Sylow join;
uniqueness is applied to LT, retaining the full original hypotheses. -/
theorem single_cubic_span_normalizer_le
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hg : let J := H ⊔ borelResidual T L
      ChapterF.IsGoldschmidtTriple
        ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J) (H.subgroupOf J))
    (c : SingleQuotientProduct T L H)
    (hYM : c.cubic_lift.map (H ⊔ borelResidual T L).subtype ≤ normalizer (L : Set G))
    (ha : ∀ (y : G) (hy : y ∈ c.cubic_lift.map (H ⊔ borelResidual T L).subtype),
      d.quotientNormalizerAction ⟨y,hYM hy⟩ = 1) :
    normalizer (conjugateSpanBy (c.cubic_lift.map (H ⊔ borelResidual T L).subtype)
      (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) := by
  let J := H ⊔ borelResidual T L
  let Y := c.cubic_lift.map J.subtype
  let X := Y ⊔ (T : Subgroup G)
  let E := conjugateSpanBy Y (T : Subgroup G)
  have hTJ : (T : Subgroup G) ≤ J := hH.1.1.2.trans (show H ≤ J from le_sup_left)
  have hXJ : X ≤ J := sup_le (map_subtype_le _) hTJ
  have hJcore : J.pCoreIn 2 ≠ ⊥ := by
    let eH : H.subgroupOf J ≃* H := subgroupOfEquivOfLe le_sup_left
    have he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :=
      ⟨(QuotientGroup.congr _ _ eH (pCore_map_iso 2 eH)).symm.trans hg.quotient_right.some⟩
    exact single_borel_join_core_ne_bot d hH hB hZ he
  have hJcoreT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using
      pCoreIn_le_sylow J (T.subtype hTJ)
  have hXcore : X.pCoreIn 2 ≠ ⊥ := by
    intro he
    apply hJcore
    apply bot_unique
    rw [←he]
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J)
      (hJcoreT.trans le_sup_right)
      ((hXJ.trans J.le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hchar := Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
    (d.hypothesis.qtke.evenCharacteristic T) ⟨hXcore,show (T : Subgroup G) ≤ X from le_sup_right⟩)
  let : Group.IsSolvable X := single_cubic_join_solvable c hH.1.1.2
  have hEX : E ≤ X := conjugateSpanBy_le le_sup_left (le_sup_right.trans X.le_normalizer)
  have hXE : X ≤ normalizer (E : Set G) :=
    sup_le ((le_conjugateSpanBy Y (T : Subgroup G)).trans E.le_normalizer)
      (le_normalizer_conjugateSpanBy Y (T : Subgroup G))
  let N := E.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer hXE
  have hEne : E ≠ ⊥ := by
    intro he
    apply single_cubic_moves_omega hH hZ hg c
    have hcent : E ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
      rw [he]
      exact bot_le
    exact (le_conjugateSpanBy Y (T : Subgroup G)).trans hcent
  have hNne : N ≠ ⊥ := by
    intro he
    apply hEne
    rw [←map_subgroupOf_eq_of_le hEX]
    exact (congrArg (map X.subtype) he).trans (Subgroup.map_bot _)
  have hcore := pCore_ne_bot_of_solvable_normal_of_characteristic 2 hchar N hNne
  have hEcore : pCore 2 E ≠ ⊥ := by
    intro he
    let e : N ≃* E := subgroupOfEquivOfLe hEX
    have hh := pCore_map_iso 2 e
    rw [he] at hh
    exact hcore ((map_eq_bot_iff_of_injective _ e.injective).mp hh)
  have hEcoreG : E.pCoreIn 2 ≠ ⊥ := fun he => hEcore
    ((map_eq_bot_iff_of_injective _ E.subtype_injective).mp he)
  have hnorm : normalizer (E : Set G) ≤ normalizer (E.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image E (pCore 2 E)
  exact hnorm.trans (normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
    (isPGroup_pCoreIn 2 E) hEcoreG ((single_cubic_span_normalized d c hYM ha).trans hnorm))

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
