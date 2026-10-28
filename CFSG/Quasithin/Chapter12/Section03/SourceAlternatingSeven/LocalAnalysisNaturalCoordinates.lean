module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNormalizer
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalLift
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison

/-!
# Full natural coordinates with the original A₇ projection

The original quasisimple two-core quotient maps onto the faithful A₇ actor.
The center-preimage theorem identifies this map's kernel with O₂,Z(L).
The two resulting A₇ markings differ by an automorphism, hence by a
seven-letter permutation. Applying that permutation to the full natural
module aligns its action with the setup's original projection.

Combined with the perfect-central-cover lift, this proves the natural
quotient branch of 12.3.3 on all of the original V. The four-dimensional
exclusion and selection of this row from 12.2.2 remain separate arguments.
Source: Aschbacher--Smith, Lemma 12.3.3, printed pp.807--808.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

/-- The actual faithful A₇ actor kills exactly the original central kernel. -/
theorem actionCentralizer_eq_centralPreimage
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7)) :
    (centralizer (V : Set G)).subgroupOf L =
      (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) := by
  let := S.chosen.actionCentralizer_normal
  let := S.hypothesis.quasisimple
  let : Nontrivial (alternatingGroup (Fin 7)) := by infer_instance
  let f := e.toMonoidHom.comp S.chosen.coreToFaithful
  have hf : Function.Surjective f := e.surjective.comp S.chosen.coreToFaithful_surjective
  have hc := IsQuasisimple.comap_center_of_surjective f hf
  rw [alternatingGroup.center_eq_bot (by simp)] at hc
  ext l
  change l ∈ (centralizer (V : Set G)).subgroupOf L ↔
    QuotientGroup.mk' (pCore 2 L) l ∈ center (L ⧸ pCore 2 L)
  rw [← hc]
  change l ∈ (centralizer (V : Set G)).subgroupOf L ↔
    e (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l) = 1
  rw [e.map_eq_one_iff]
  exact (QuotientGroup.eq_one_iff l).symm

/-- Any faithful seven-letter natural marking can be aligned with the given
central-quotient marking, without collapsing the original central cover. -/
theorem naturalCoordinates_of_fullAction
    (a : letI := S.chosen.actionCentralizer_normal
      ActionEquiv S.chosen.faithfulAction (alternatingNatural 7)) :
    Nonempty S.NaturalCoordinates := by
  let := S.chosen.actionCentralizer_normal
  let e : CentralQuotient L ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq
      (S.actionCentralizer_eq_centralPreimage a.groupEquiv).symm).trans a.groupEquiv
  let φ : MulAut (alternatingGroup (Fin 7)) := e.symm.trans S.quotient
  let s := BinaryPermutation.SevenNormalizer.permutationOfAut φ
  let π : L →* alternatingGroup (Fin 7) :=
    a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' _)
  have hφ (l : L) : φ (π l) = S.projection l := by
    change S.quotient (e.symm (e (QuotientGroup.mk' _ l))) = _
    rw [e.symm_apply_apply]
    rfl
  have hs (l : L) : (S.projection l).val = s * (π l).val * s⁻¹ := by
    rw [← hφ]
    exact (congrArg (fun α : MulAut (alternatingGroup (Fin 7)) => (α (π l)).val)
      (BinaryPermutation.SevenNormalizer.conjugation_permutationOfAut φ)).symm
  let b := a.linearEquiv.trans evenWordsEquivNatural.symm
  have hb (l : L) (v : S.chosen.space) :
      b (S.chosen.chosenAction l v) = evenRepresentation (π l).val (b v) := by
    apply evenWordsEquivNatural.injective
    change evenWordsEquivNatural (evenWordsEquivNatural.symm
      (a.linearEquiv (S.chosen.chosenAction l v))) = _
    rw [evenWordsEquivNatural.apply_symm_apply, evenWordsEquivNatural_equivariant]
    change a.linearEquiv (S.chosen.chosenAction l v) =
      BinaryPermutation.naturalRepresentation (Fin 7) (π l).val
        (evenWordsEquivNatural (evenWordsEquivNatural.symm (a.linearEquiv v)))
    rw [evenWordsEquivNatural.apply_symm_apply]
    exact a.intertwines (QuotientGroup.mk' _ l) v
  let c := b.trans (LinearMap.GeneralLinearGroup.toLinearEquiv
    (evenRepresentation.asGroupHom s))
  let E := S.chosen.spaceEquiv.symm.trans c.toAddEquiv.toMultiplicative
  refine ⟨⟨E, ?_⟩⟩
  intro l v
  let w := (S.chosen.spaceEquiv.symm v).toAdd
  have hw : (w.val.toMul.val : G) = (v : G) :=
    (S.chosen.spaceEquiv_apply w).symm.trans
      (congrArg Subtype.val (S.chosen.spaceEquiv.apply_symm_apply v))
  have hv : (S.chosen.spaceEquiv.symm
      (V.normalizerMonoidHom ⟨l, S.chosen.normalizes l.property⟩ v)).toAdd =
        S.chosen.chosenAction l w := by
    apply Multiplicative.ofAdd.injective
    apply S.chosen.spaceEquiv.injective
    simp only [ofAdd_toAdd, S.chosen.spaceEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [S.chosen.spaceEquiv_apply]
    change (l : G) * (v : G) * (l : G)⁻¹ =
      (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹
    rw [hw]
  change evenRepresentation s (b ((S.chosen.spaceEquiv.symm
    (V.normalizerMonoidHom ⟨l, S.chosen.normalizes l.property⟩ v)).toAdd)) =
      evenRepresentation (S.projection l).val (evenRepresentation s (b w))
  rw [hv, hb, hs]
  change (evenRepresentation s * evenRepresentation (π l).val) (b w) =
    (evenRepresentation (s * (π l).val * s⁻¹) * evenRepresentation s) (b w)
  rw [← map_mul, ← map_mul]
  congr 2
  group

/-- The natural-quotient branch of original 12.3.3, including the cohomological
lift and compatibility with the original O₂,Z quotient. -/
theorem naturalCoordinates_of_naturalQuotient
    (a : letI := S.chosen.actionCentralizer_normal
      ActionEquiv S.chosen.faithfulCentralAction (alternatingNatural 7)) :
    Nonempty S.NaturalCoordinates := by
  obtain ⟨b⟩ := S.chosen.fullAction_of_odd_alternating_quotient (by decide) (by decide) a
  exact S.naturalCoordinates_of_fullAction b

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
