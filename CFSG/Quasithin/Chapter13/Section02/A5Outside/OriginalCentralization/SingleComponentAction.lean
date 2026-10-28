module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleCubicSpan
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentLiftAction

/-!
# The original normal component normalizes the cubic span

The selected normal component and the selected cubic commute modulo O₂(J),
by lifting across the full O₃′(J) kernel. Their commutator bound persists
under the original Sylow conjugates. The span is two-perfect and O₂(J)
normalizes it, so the normalizing two-group error can be removed.

The same cubic and Sylow supplement the same normal lift. The existing
full span-normalizer bound therefore places H in N_G(L), contradicting
its original outside placement. This completes the single-factor
Goldschmidt endgame without an added normalization premise.

Source: Aschbacher--Smith 13.2.7, printed pp.883--884.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L H : Subgroup G}

/-- The normal lift normalizes the actual Sylow-conjugate cubic span.
Commutation is lifted across the full prime-to-three core before the
normalizing two-group error is removed. -/
theorem single_component_normalizes_cubic_span
    (hTH : (T : Subgroup G) ≤ H)
    (hg : let J := H ⊔ borelResidual T L
      ChapterF.IsGoldschmidtTriple
        ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J) (H.subgroupOf J))
    (hsq : IsSQTK KnownSimple.IsKnownSimple (H ⊔ borelResidual T L : Subgroup G))
    (c : SingleQuotientProduct T L H) :
    c.lift.map (H ⊔ borelResidual T L).subtype ≤ normalizer
      (conjugateSpanBy (c.cubic_lift.map (H ⊔ borelResidual T L).subtype)
        (T : Subgroup G) : Set G) := by
  let J := H ⊔ borelResidual T L
  let K := c.lift.map J.subtype
  let Y := c.cubic_lift.map J.subtype
  let E := conjugateSpanBy Y (T : Subgroup G)
  let Q := J.pCoreIn 2
  let : c.lift.Normal := c.lift_normal
  have hTJ : (T : Subgroup G) ≤ J := hTH.trans le_sup_left
  have hJK : J ≤ normalizer (K : Set G) := by
    intro x hx
    exact le_normalizer_map J.subtype
      (mem_map_of_mem J.subtype (show (⟨x,hx⟩ : J) ∈ normalizer (c.lift : Set J) from
        le_normalizer_of_normal (mem_top _)))
  have hJQ : J ≤ normalizer (Q : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hc : ⁅c.cubic_lift,c.lift⁆ ≤ pCore 2 J := by
    apply ChapterF.SourceAssembly.normal_component_lift_commutator_le_twoCore hg hsq c.lift c.cubic_lift c.lift_component
      (c.lift_image.symm ▸ c.selected.isComponent)
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [c.cubic_image,c.lift_image]
    exact inf_le_right
  have hYK : ⁅Y,K⁆ ≤ Q := by
    change ⁅c.cubic_lift.map J.subtype,c.lift.map J.subtype⁆ ≤
      (pCore 2 J).map J.subtype
    rw [←map_commutator]
    exact map_mono hc
  have hYP : Y ≤ commutatorPreimage J K Q := le_commutatorPreimage (map_subtype_le _) hYK
  have hEP : E ≤ commutatorPreimage J K Q := conjugateSpanBy_le hYP
    (commutatorPreimage_normalized J K Q (T : Subgroup G) hJQ
      (hTJ.trans J.le_normalizer) (hTJ.trans hJK) (hTJ.trans hJQ))
  have hKE : ⁅K,E⁆ ≤ Q := by
    rw [commutator_comm]
    exact (commutator_mono hEP le_rfl).trans (commutator_commutatorPreimage_le J K Q hJQ)
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using
      pCoreIn_le_sylow J (T.subtype hTJ)
  have hcY : Nat.card Y = 3 :=
    (card_map_of_injective J.subtype_injective).trans c.cubic_card
  have hp : IsPPerfect 2 E := isPPerfect_conjugateSpanBy_of_coprime Y (T : Subgroup G)
    (by rw [hcY]; decide)
  exact le_normalizer_of_isPPerfect_of_commutator_le E K Q hp (isPGroup_pCoreIn 2 J)
    (hQT.trans (le_normalizer_conjugateSpanBy Y (T : Subgroup G))) hKE

/-- The literal selected cubic, normal lift and original Sylow generate J. -/
theorem single_cubic_component_generates
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hg : let J := H ⊔ borelResidual T L
      ChapterF.IsGoldschmidtTriple
        ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J) (H.subgroupOf J))
    (c : SingleQuotientProduct T L H) :
    c.lift.map (H ⊔ borelResidual T L).subtype ⊔
      (c.cubic_lift.map (H ⊔ borelResidual T L).subtype ⊔ (T : Subgroup G)) =
      H ⊔ borelResidual T L := by
  let J := H ⊔ borelResidual T L
  let B := H.subgroupOf J
  have hTJ : (T : Subgroup G) ≤ J := hH.1.1.2.trans (show H ≤ J from le_sup_left)
  let S := T.subtype hTJ
  let : c.lift.Normal := c.lift_normal
  have hSB : (S : Subgroup J) ≤ B := fun x hx => hH.1.1.2 hx
  have hi : (S : Subgroup J).relIndex B = 3 :=
    SymmetricThreeTwoCore.sylow_index_three hg.quotient_right.some (S.subtype hSB)
  let q := QuotientGroup.mk' (pPrimeCore 3 J)
  have hd : Disjoint c.cubic_lift c.lift := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    have hqx : q x = 1 := by
      apply mem_bot.mp
      apply (disjoint_iff.mp c.disjoint).le
      refine ⟨?_,?_⟩
      · rw [←c.lift_image]
        exact mem_map_of_mem q hx.2
      · rw [←c.cubic_image]
        exact mem_map_of_mem q hx.1
    have hk : x ∈ pPrimeCore 3 J := (QuotientGroup.eq_one_iff x).mp hqx
    have hcop : Nat.Coprime (Nat.card c.cubic_lift) (Nat.card (pPrimeCore 3 J)) := by
      rw [c.cubic_card]
      exact pPrimeCore_coprime_card
    exact (disjoint_iff.mp (disjoint_of_coprime_natCard hcop)).le ⟨hx.1,hk⟩
  have he := normal_cubic_sylow_supplement c.lift B c.cubic_lift S
    (single_component_sup_H hH hg c) hSB hi c.cubic_card hd c.cubic_permutes.symm
  have hm := congrArg (map J.subtype) he
  simpa only [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
    S,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using hm

/-- The original single-factor product is impossible: its normal lift and
cubic Sylow supplement all normalize the same span, placing H in N_G(L). -/
theorem single_product_false
    {V V₁ V₂ V₃ : Subgroup G} (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hsq : IsSQTK KnownSimple.IsKnownSimple (H ⊔ borelResidual T L : Subgroup G))
    (hg : let J := H ⊔ borelResidual T L
      ChapterF.IsGoldschmidtTriple
        ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J) (H.subgroupOf J))
    (c : SingleQuotientProduct T L H)
    (hn : normalizer (conjugateSpanBy
      (c.cubic_lift.map (H ⊔ borelResidual T L).subtype) (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) : False := by
  have hJ : H ⊔ borelResidual T L ≤ normalizer (L : Set G) := by
    rw [←single_cubic_component_generates hH hg c]
    refine sup_le ((single_component_normalizes_cubic_span hH.1.1.2 hg hsq c).trans hn)
      (sup_le ?_ d.normalizes_L)
    exact ((le_conjugateSpanBy _ _).trans
      (conjugateSpanBy (c.cubic_lift.map (H ⊔ borelResidual T L).subtype)
        (T : Subgroup G)).le_normalizer).trans hn
  exact hH.1.2 (le_sup_left.trans hJ)


/-- The original single-factor quotient is excluded with both literal
Goldschmidt triples, their intersection and the full O₃′ kernel retained. -/
theorem single_original_quotient_false
    {V V₁ V₂ V₃ : Subgroup G} (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let J := H ⊔ borelResidual T L
    let A := (borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J
    let B := H.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    IsSQTK KnownSimple.IsKnownSimple J →
    ChapterF.IsGoldschmidtTriple A B →
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) →
    A.map q ⊓ B.map q = ((T : Subgroup G).subgroupOf J).map q →
    pCore 2 (J ⧸ pPrimeCore 3 J) = ⊥ → False := by
  intro J A B q hsq hg hqg hi hcore
  obtain ⟨c⟩ := single_quotient_prime_product d hH hB hZ hsq hg hqg hcore
  have hn := single_cubic_le_normalizer d hH hB hZ hg c
  have ha := single_original_cubic_quotient_action d hH hB hZ hg hqg hi hcore c
  exact single_product_false d hH hsq hg c
    (single_cubic_span_normalizer_le d hH hB hZ hg c hn ha)

/-- Original 13.2.7 in the single-factor case: every original H whose
literal two-core quotient is S₃ fixes the full Sylow omega-center. The
original and quotient Goldschmidt triples are constructed internally. -/
theorem single_outside_centralizes_omega
    {V V₁ V₂ V₃ : Subgroup G} (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  by_contra hZ
  have hs : Group.IsSolvable H := SymmetricThreeTwoCore.solvable he.some
  obtain ⟨hi,hqg,hcore,_⟩ := single_borel_quotient_amalgam d hH hZ he
    (not_three_borel_quotient d hH hB hZ hs)
  exact single_original_quotient_false d hH hB hZ
    (single_borel_join_sqtk d hH hB hZ he)
    (single_borel_goldschmidt_triple d hH hZ he) hqg hi hcore

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
