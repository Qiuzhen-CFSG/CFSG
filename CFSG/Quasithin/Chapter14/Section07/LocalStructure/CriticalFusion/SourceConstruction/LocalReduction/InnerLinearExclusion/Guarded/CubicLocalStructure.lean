module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicLocalStructure
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded.CubicGeometry

/-!
# Same-group structural-input version

This proof uses only `Structural1222At` and `Theorem12213At` at the original G,T.
It preserves the literal groups and quotient maps of the source argument below.

# A nontrivial core for the original cubic completion

The original elementary span U is larger than the rank-three seed V,
is contained in T, and is normal in YT. If D = ⟨L₂,Y,T⟩ had trivial
two-core, the marked Goldschmidt classification and the rank of U would
select the Aut(M₁₂) amalgam. The centered vertex has no normal elementary
two-subgroup of rank four, contradicting the actual U inside YT.

Consequently D is a local subgroup of characteristic two. The original
point V₁ centralizes T, so its D-span W lies in Z(O₂(D)) and is elementary
abelian. All marked-amalgam inputs are supplied by their source proofs.

Source: Aschbacher–Smith, 14.5.5 and 14.5.7(3), printed pp.1013--1014,
and B.2.14, printed p.78, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Escape of G₁ forces its original elementary span to be larger than the seed. -/
private theorem span_card_gt_eight
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T) :
    8 < Nat.card F.U := by
  have hVU : V ≤ F.U := le_conjugateSpanBy _ _
  have hne : V ≠ F.U := by
    intro he
    apply h.flag_escape_at F previous
    have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
      intro X _ _ hX S M hM
      exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
    apply le_trans _ (h.seed_normalizer_le_at structural)
    have hh : F.H ≤ normalizer (F.U : Set G) := le_normalizer_conjugateSpanBy _ _
    exact hh.trans_eq (congrArg (fun A : Subgroup G => normalizer (A : Set G)) he).symm
  by_contra! hc
  apply hne
  apply eq_of_le_of_card_ge hVU
  simpa only [h.seed_card, show (2 : ℕ) ^ 3 = 8 from rfl] using hc

/-- Source 14.5.5 on the original generated group: a core-free marked
amalgam cannot contain the large normal elementary span at its centered vertex. -/
theorem cubic_generated_core_ne_bot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    pCore 2 (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G) ≠ ⊥ := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let A := (F.P L).subgroupOf D
  let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
  have ht := cubic_goldschmidt_triple h structural Y hYH he
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hUT : F.U ≤ (T : Subgroup G) :=
    (IsElementaryAbelian.isPGroup 2 F.U).le_sylow_of_normalized T
      ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))
  have hUD : F.U ≤ D := hUT.trans hTD
  have hYTH : Y ⊔ (T : Subgroup G) ≤ F.H := sup_le hYH (F.invariant 1)
  have hnorm : Y ⊔ (T : Subgroup G) ≤ normalizer (F.U : Set G) :=
    hYTH.trans (le_normalizer_conjugateSpanBy V F.H)
  let U₀ := F.U.subgroupOf D
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.subgroupOf hUD
  have hUB : U₀ ≤ B := fun x hx => (le_sup_right : (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G)) (hUT hx)
  let E := U₀.subgroupOf B
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hUB
  let : E.Normal := normal_subgroupOf_of_le_normalizer
    ((show B ≤ (normalizer (F.U : Set G)).comap D.subtype from fun x hx => hnorm hx).trans
      (le_normalizer_comap D.subtype))
  let eU := (subgroupOfEquivOfLe hUB).trans (subgroupOfEquivOfLe hUD)
  have hcard : 8 < Nat.card E := by
    rw [Nat.card_congr eU.toEquiv]
    exact span_card_gt_eight h structural previous
  have hr : 4 ≤ primeRank 2 D := by
    by_contra! hr
    have hc := (primeRank_le_iff_elementary_card_le D).mp (show primeRank 2 D ≤ 3 by omega)
      U₀ inferInstance
    rw [Nat.card_congr (subgroupOfEquivOfLe hUD).toEquiv] at hc
    have hh := span_card_gt_eight (F := F) h structural previous
    norm_num at hc
    omega
  have hZ : center B ≠ ⊥ := by
    obtain ⟨z,hz,hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
    have hzP : z ∈ F.Vi 1 := hpoint ▸ mem_zpowers z
    have hzT : z ∈ (T : Subgroup G) := h.chosen.le_sylow (F.le_seed 1 hzP)
    let b : B := ⟨⟨z,hTD hzT⟩,(le_sup_right : (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G)) hzT⟩
    have hb : b ∈ center B := by
      apply mem_center_iff.mpr
      intro a
      apply Subtype.ext
      apply Subtype.ext
      exact (mem_centralizer_iff.mp
        ((hYTH.trans (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
          a.property) z hzP).symm
    intro hzbot
    have heq := congrArg (fun a : B => (a.val : G)) (mem_bot.mp (hzbot ▸ hb))
    exact hz heq
  intro hcore
  have hc : ChapterF.SourceAssembly.CharacteristicTwoMarkedAmalgamInput.{u} :=
    ChapterF.SourceAssembly.characteristicTwoMarked_of_large_nonabelian
      ChapterF.SourceAssembly.Goldschmidt.largeNonabelianMarkedAmalgams
  obtain hm | hm := ht.aut_mathieu_marked_of_high_rank hc hcore hr
  all_goals
    have hrE : primeRank 2 E ≤ 3 := by
      first
      | exact ChapterF.SourceAssembly.Mathieu.outer_centered_parabolic_normal_elementary_primeRank_le_three
          hm B (Or.inr rfl) hZ E
      | exact ChapterF.SourceAssembly.Mathieu.outer_centered_parabolic_normal_elementary_primeRank_le_three
          hm B (Or.inl rfl) hZ E
    have hu : Nat.card E ≤ 2 ^ 3 := by
      rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 2) E]
      exact Nat.pow_le_pow_right (by decide) hrE
    norm_num at hu
    omega

/-- The actual point span is elementary and lies in the center of the
nontrivial two-core of the source Goldschmidt completion. -/
theorem cubic_generated_local_structure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    D ∈ Chapter1.He G ∧ IsSQTK KnownSimple.IsKnownSimple D ∧
      IsElementaryAbelian 2 W ∧ W ≤ D.pCoreIn 2 ∧
      W ≤ centralizer (D.pCoreIn 2 : Set G) := by
  let := h.chosen.elementary
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hZD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hWD : W ≤ D := conjugateSpanBy_le_self hZD
  have hn := cubic_generated_core_ne_bot h hab structural previous Y hYH he
  have hDH : D ∈ Chapter1.H G := by
    intro hz
    exact hn (((pCore 2 D).map_eq_bot_iff_of_injective D.subtype_injective).mp hz)
  have hHe : D ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 T
    (h.source.simpleQTKE.evenCharacteristic T) ⟨hDH,hTD⟩
  have hQT : D.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hq := pCoreIn_le_sylow D (T.subtype hTD)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD] using hq
  have hZC : F.Vi 1 ≤ centralizer (T : Set G) :=
    le_centralizer_iff.mp ((F.invariant 1).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  have hQC : W ≤ centralizer (D.pCoreIn 2 : Set G) :=
    conjugateSpanBy_le (hZC.trans (centralizer_le hQT))
      ((D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D))).trans
        (normalizer_le_normalizer_centralizer _))
  have hWQ : W ≤ D.pCoreIn 2 := (le_inf hWD hQC).trans hHe
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp
    (hQC.trans (centralizer_le hWQ))
  exact ⟨hHe,Chapter3.sqtk_of_mem_H h.source.simpleQTKE hDH,
    conjugateSpanBy_elementary_of_commutative _ _,hWQ,hQC⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Guarded
