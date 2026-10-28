module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Source
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerNonalternatingG2
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions

/-!
# The G₂ block from the original escaping Sylow normalizer

The actual pair (LT,T) satisfies all small MS-pair hypotheses: uniqueness
supplies the characteristic-subgroup obstruction, and the proper Sylow
subgroup supplies MS2(a). The centerless G₂ marking identifies the central
core quotient with the original quotient by O₂(L). Whole-core reconstruction
then gives the G₂ block and its moving-centralizer application.

Source: Aschbacher–Smith, 3.3.6(d), the paragraph before 3.3.23 and
3.3.27, printed pp.588,598–600; C.1.31–32, printed pp.135–136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original escaping configuration supplies the literal small MS-pair;
the rank-two marking is its only additional source input. -/
theorem smallMSPair_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hrank : SmallRankTwoQuotient L) :
    SmallMSPair KnownSimple.IsKnownSimple L (T : Subgroup G) := by
  have hHN : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer D.sylow_normalizes_component
  have hsq := h.toHypothesis1221.sylow_normalized_sqtk D.sylow_normalizes_component
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hc := h.toHypothesis1221.sylow_normalized_component D.sylow_normalizes_component
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  refine ⟨inferInstance, (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
    (hsq.subgroup _), generalizedFitting_eq_pCore_of_selfCentralizing 2
      (join_characteristicTwo h), ?_,
    hc.subgroupOf_of_le le_sup_left hHN, hrank, ?_, ?_⟩
  · let : (L.subgroupOf (L ⊔ (T : Subgroup G))).Normal :=
      normal_subgroupOf_of_le_normalizer hHN
    intro g hg
    have hm : (⟨g, hg⟩ : (L ⊔ (T : Subgroup G) : Subgroup G)) ∈
        L.subgroupOf (L ⊔ (T : Subgroup G)) ⊔
          (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) := by
      rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
      trivial
    obtain ⟨l, hl, t, ht, he⟩ := mem_sup_of_normal_left.mp hm
    exact ⟨l, hl, t, ht, congrArg Subtype.val he⟩
  · apply sylow_msOddIndex
    · refine ⟨T.subtype le_sup_right, ?_⟩
      simpa only [Sylow.coe_subtype] using
        map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤
          L ⊔ (T : Subgroup G) from le_sup_right)
    · refine lt_of_le_of_ne le_sup_right ?_
      intro he
      have hLT : L ≤ (T : Subgroup G) := he.symm ▸ le_sup_left
      let := h.quasisimple
      let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) :=
        h.quasisimple.simple
      have : Nontrivial (L ⧸ pCore 2 L) :=
        (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
      exact Group.IsPerfect.not_isNilpotent (L ⧸ pCore 2 L)
        ((T.isPGroup'.to_le hLT).to_quotient (pCore 2 L)).isNilpotent
  · intro C hC hn
    let := hC
    exact characteristic_eq_bot_of_escape h D hescape C
      ((normal_subgroupOf_iff_le_normalizer
        ((map_subtype_le C).trans le_sup_right)).mp hn)

private def g2CentralCoreMarking
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)) := by
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact e.map_eq_one_iff.mp
      (Atlas.G2.BinaryLocalResidual.center_eq_bot.le ((centerCongr e ⟨x, hx⟩).property))
  have hcp : centralPreimage (pCore 2 L) = pCore 2 L := by
    change (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) = pCore 2 L
    rw [hz]
    exact QuotientGroup.ker_mk' _
  exact (QuotientGroup.quotientMulEquivOfEq hcp).trans e

/-- Whole-core G₂ reconstruction in the original Chapter 12 configuration.
No no-escape or fixed-space premise is needed for the block itself. -/
theorem g2Two_block_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ChapterC.IsG2TwoBlock L := by
  let eC := g2CentralCoreMarking e
  have hms := smallMSPair_of_escape h D hescape (Or.inr (Or.inr ⟨eC⟩))
  have r := g2Reconstruction_knownSimple G L (T : Subgroup G) hms eC
  obtain ⟨m⟩ := r.model
  exact ChapterC.IsG2TwoBlock.of_model
    (hms.short_of_core r.elementary r.central h.quasisimple m.g2_irreducible) ⟨m⟩

/-- The actual Weyl-action marking supplies the quotient marking used by
whole-core reconstruction. -/
theorem g2Two_block_of_weyl_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (e : ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2))) :
    ChapterC.IsG2TwoBlock L :=
  g2Two_block_of_escape h D hescape e.groupEquiv

/-- Application to the literal 3.3.27 centralizer clauses, discharging its
block premise from the original Weyl-action marking. -/
theorem g2Two_source_movement_centralizer_of_weyl_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (e : ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
      (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2))) :
    let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
    IsElementaryAbelian 2 C ∧
      ∃ A : Subgroup G, A ≤ normalizer (T : Set G) ∧ Odd (Nat.card A) ∧
        ∃ d ∈ A, d ∉ normalizer (L : Set G) ∧
          ¬ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj d⁻¹).toMonoidHom ≤
            (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          C ⊓ C.map (MulAut.conj d⁻¹).toMonoidHom = ⊥ ∧
          C.map (MulAut.conj d⁻¹).toMonoidHom ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
  g2Two_source_movement_centralizer h D hfixed hescape
    (g2Two_block_of_weyl_model h D hescape e)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
