module
public import CFSG.Quasithin.Chapter4.Section01.CharacteristicControl
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
import Mathlib.Tactic
/-!
# The actual residual section-centralizer Sylow subgroup

A.4.3 compares signalizers across X=Y O2(X). This transfers the already
constructed Sylow subgroup of the X-section centralizer to the Y-section
centralizer, retaining its ambient image. The full characteristic-normalizer
bound then promotes this relative Sylow subgroup from H intersect M to H.
Source: Aschbacher--Smith,4.1.4(4), printed p.607.
-/

public section
namespace CFSG.Quasithin.Chapter4
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem le_of_sylow_image {R C Q : Subgroup G}
    (hR : ∃ S : Sylow 2 C, (S : Subgroup C).map C.subtype = R)
    (hp : IsPGroup 2 Q) (hQC : Q ≤ C) (hRQ : R ≤ Q) : Q ≤ R := by
  obtain ⟨S,rfl⟩ := hR
  have hs : (S : Subgroup C) ≤ Q.subgroupOf C := fun x hx => hRQ ⟨x,hx,rfl⟩
  have he := S.is_maximal' hp.comap_subtype hs
  intro q hq
  exact ⟨⟨q,hQC hq⟩,he ▸ hq,rfl⟩

/-- A covering residual has the same Sylow section-centralizer subgroup.
The proof uses the actual core intersection and A.4.3 signalizer comparison. -/
theorem sylow_sectionCentralizer_of_cover {M X A Y R : Subgroup G}
    (hXM : X ≤ M) (hXN : (X.subgroupOf M).Normal) (hX : IsPPerfect 2 X)
    (hAM : A ≤ M) (hYA : Y ≤ A) (hYX : Y ≤ X)
    (hYN : (Y.subgroupOf A).Normal) (hY : IsPPerfect 2 Y)
    (hcover : (X : Set G) = (Y : Set G) * (X.pCoreIn 2 : Set G))
    (hR : ∃ S : Sylow 2 (sectionCentralizerIn A X),
      (S : Subgroup (sectionCentralizerIn A X)).map
        (sectionCentralizerIn A X).subtype = R) :
    ∃ S : Sylow 2 (sectionCentralizerIn A Y),
      (S : Subgroup (sectionCentralizerIn A Y)).map
        (sectionCentralizerIn A Y).subtype = R := by
  obtain ⟨S,hS⟩ := hR
  have hRp : IsPGroup 2 R := hS ▸ S.isPGroup'.map (sectionCentralizerIn A X).subtype
  have hRC : R ≤ sectionCentralizerIn A X := hS ▸ map_subtype_le _
  have hAN := (normal_subgroupOf_iff_le_normalizer hYA).mp hYN
  have hQ : X.pCoreIn 2 ⊓ Y ≤ Y.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 X).to_le inf_le_left) inf_le_right
    exact (le_inf (hYX.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))) Y.le_normalizer).trans
        inf_normalizer_le_normalizer_inf
  have hRY : R ≤ sectionCentralizerIn A Y := by
    refine le_inf (hRC.trans inf_le_left) ((le_sectionCentralizer_iff R Y).mpr ⟨?_,?_⟩)
    · exact (hRC.trans inf_le_left).trans hAN
    · apply le_trans (le_inf ?_ ?_) hQ
      · exact (commutator_mono (hRC.trans inf_le_right) hYX).trans
          ((le_sectionCentralizer_iff (sectionCentralizer X) X).mp le_rfl).2
      · exact le_normalizer_iff_commutator_le_right.mp ((hRC.trans inf_le_left).trans hAN)
  obtain ⟨P,hRP⟩ := (hRp.comap_subtype : IsPGroup 2 (R.subgroupOf (sectionCentralizerIn A Y))).exists_le_sylow
  let Q := (P : Subgroup (sectionCentralizerIn A Y)).map (sectionCentralizerIn A Y).subtype
  have hRQ : R ≤ Q := fun r hr => ⟨⟨r,hRY hr⟩,hRP hr,rfl⟩
  have hQM : Q ≤ M := (map_subtype_le _).trans (inf_le_left.trans hAM)
  have hp : ∃ P' : Sylow 2 (ChapterA.Section04.twoSectionCentralizer Y A),
      (P' : Subgroup (ChapterA.Section04.twoSectionCentralizer Y A)).map
        (ChapterA.Section04.twoSectionCentralizer Y A).subtype = Q := by
    rw [← sectionCentralizerIn_eq_twoSectionCentralizer]
    exact ⟨P,rfl⟩
  have hmax := (ChapterA.Section04.maximal_signalizer_iff_sylow Y A Q
    hYA hYN.isSubnormal hY).mpr hp
  have hsig := ((ChapterA.Section04.isMaximalTwoSignalizer_iff Y A Q).mp hmax).1
  have hsigM : ChapterA.Section04.IsTwoSignalizer Y M Q :=
    (ChapterA.Section04.isTwoSignalizer_iff _ _ _).mpr ⟨hQM,hsig.isPGroup,hsig.normalizes⟩
  have hjoin : X = (X ⊓ Y) ⊔ X.pCoreIn 2 := by
    apply le_antisymm
    · intro x hx
      obtain ⟨y,hy,q,hq,rfl⟩ := hcover ▸ (show x ∈ (X : Set G) from hx)
      exact mul_mem_sup ⟨hYX hy,hy⟩ hq
    · exact sup_le inf_le_left (pCoreIn_le 2 X)
  have hQC : Q ≤ sectionCentralizerIn A X := by
    have ht := ChapterA.Section04.signalizer_le_section_of_core_join X Y M Q
      hXM hXN.isSubnormal hX hjoin hsigM
    rw [← sectionCentralizerIn_eq_twoSectionCentralizer] at ht
    exact le_inf ((map_subtype_le _).trans inf_le_left) (ht.trans inf_le_right)
  exact ⟨P,le_antisymm (le_of_sylow_image ⟨S,hS⟩ hsig.isPGroup hQC hRQ) hRQ⟩

/-- Full4.1.4(4), first inside H∩M and then in H, with the source
Hplus=O²(X∩H) and literal R=O2(I). -/
theorem lemma_4_1_4_4 {K : GroupClass} {T : Sylow 2 G}
    {M X Mminus I H : Subgroup G} (hyp : Hypothesis411 K T M X)
    (hminus : Mminus ∈ sigma M X) (hI : I ∈ muStar M X Mminus)
    (hH : H ∈ Chapter1.H G) (hIH : I ≤ H) (hout : ¬ H ≤ M) :
    let Y := (pResidual 2 (X ⊓ H : Subgroup G)).map (X ⊓ H).subtype
    (∃ S : Sylow 2 (sectionCentralizerIn (H ⊓ M) Y),
      (S : Subgroup (sectionCentralizerIn (H ⊓ M) Y)).map
        (sectionCentralizerIn (H ⊓ M) Y).subtype = I.pCoreIn 2) ∧
    (∃ S : Sylow 2 (sectionCentralizerIn H Y),
      (S : Subgroup (sectionCentralizerIn H Y)).map
        (sectionCentralizerIn H Y).subtype = I.pCoreIn 2) := by
  let Y := (pResidual 2 (X ⊓ H : Subgroup G)).map (X ⊓ H).subtype
  obtain ⟨hcover,hY,hYN⟩ := lemma_4_1_4_3 hyp hI.1.1 hIH
  have hs := sylow_sectionCentralizer_of_cover hyp.plus_le hyp.plus_normal hyp.plus_perfect
    (show H ⊓ M ≤ M from inf_le_right) hY ((map_subtype_le _).trans inf_le_left)
    hYN (isPPerfect_embedded_pResidual 2 (X ⊓ H)) hcover
    (core_sylow_sectionCentralizer_outside hyp hminus hI hH hIH hout)
  refine ⟨hs,?_⟩
  have hn : normalizer (I.pCoreIn 2 : Set G) ≤ M :=
    (normalizer_le_characteristicNormalizerClosure_self _ hI.1.1.2.2.2).trans
      (lemma_4_1_4_2 hyp hminus hI)
  apply exists_sylow_eq_of_relative_normalizer_le hs
  · exact inf_le_inf_right _ inf_le_left
  · intro x hx
    exact ⟨⟨hx.1.1,hn hx.2⟩,hx.1.2⟩
end CFSG.Quasithin.Chapter4
