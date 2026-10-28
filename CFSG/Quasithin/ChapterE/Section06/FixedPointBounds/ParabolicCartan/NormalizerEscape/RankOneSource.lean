module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.RankOne
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.BenderHall.Reduction
public import Theory.SpecificGroups.SL2.EvenCentralKernel
public import Theory.SpecificGroups.Suzuki.SchurCoverReduction
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Full Hall escape in the original single rank-one component

The actual comparison from the component modulo O₂ to its marked PSL₂ or
Suzuki source image is a perfect central cover. Its kernel is a two-group,
including the exceptional small fields. Full-Borel escape therefore lifts
through this map and then through the original ambient two-core quotient.
Every prescribed odd-primary subgroup of the maximal subgroup is retained.

Source: Aschbacher–Smith E.2.2(2a), I.1.3, and 4.4.13(1), pp.215–216,407,623–624.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
open MarkedModels MarkedModels.DiagramHall ChapterB
variable {X : Type*} [Group X] [Finite X]

/-- The literal rank-one comparison has a two-group kernel. -/
theorem rank_one_comparison_kernel_isTwoGroup
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : SingleClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hm : ExchangedModel (minimalParabolicMax S hP) K f) :
    IsPGroup 2 (linearSourceComparison S hP K).ker := by
  let := hqK
  let : IsQuasisimple (actorImage K) :=
    IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  rcases hm with ⟨F,hfield,hfin,hchar,hf,hF,e,_⟩ | ⟨m,hm,_,e,_⟩
  · let := hfield
    let := hfin
    let := hchar
    let r := e.toMonoidHom.comp (linearSourceComparison S hP K)
    have hk : r.ker = (linearSourceComparison S hP K).ker :=
      MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective
    let c : PerfectCentralCovering.Cover (actorImage K)
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      { r with
        surjective := e.surjective.comp (linearSourceComparison_surjective S hP K)
        isPerfect := inferInstance
        ker_le_center := hk ▸ linearSourceComparison_central S hP K hc }
    have hh := Theory.SL2.perfect_central_kernel_isTwoGroup f hf hF c
    change IsPGroup 2 r.ker at hh
    rwa [hk] at hh
  · let r := e.toMonoidHom.comp (linearSourceComparison S hP K)
    have hk : r.ker = (linearSourceComparison S hP K).ker :=
      MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective
    let c : PerfectCentralCovering.Cover (actorImage K)
        (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
      { r with
        surjective := e.surjective.comp (linearSourceComparison_surjective S hP K)
        isPerfect := inferInstance
        ker_le_center := hk ▸ linearSourceComparison_central S hP K hc }
    have hh := BenderSuzuki.MatrixGroups.SchurCover.kernel_isTwoGroup (by omega) c
    change IsPGroup 2 r.ker at hh
    rwa [hk] at hh

/-- The original single rank-one row gives escape for every prescribed
odd-primary subgroup of its maximal subgroup. -/
theorem rank_one_original_escape
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : SingleClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hm : ExchangedModel (minimalParabolicMax S hP) K f)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup X) (hA : IsPGroup p A) (hAM : A ≤ minimalParabolicMax S hP) :
    ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  have hAK : A ≤ K := by
    rw [BenderHall.SingleClauses.component_eq_residual hc hK]
    intro a ha
    apply mem_pResidual_of_orderOf_coprime
    simpa only [Subgroup.orderOf_mk] using
      (hA.orderOf_coprime hp.coprime_two_right (⟨a,ha⟩ : A)).symm
  let q := QuotientGroup.mk' (pCore 2 X)
  let r := linearSourceComparison S hP K
  let Aq : Subgroup (actorImage K) := (A.map q).subgroupOf (actorImage K)
  let Mq := ((minimalParabolicMax S hP).map q).subgroupOf (actorImage K)
  have hpre : (componentOverlap (minimalParabolicMax S hP) K).comap r = Mq := by
    have hid : (MulEquiv.refl (sourceImage (minimalParabolicMax S hP) K)).toMonoidHom.comp r = r := by
      ext x
      rfl
    have hh := Inverted.comparison_borel_preimage S hP K (MulEquiv.refl _)
      (componentOverlap (minimalParabolicMax S hP) K) (by simp)
    change (componentOverlap (minimalParabolicMax S hP) K).comap
      ((MulEquiv.refl _).toMonoidHom.comp r) = Mq at hh
    rwa [hid] at hh
  have hAqM : Aq ≤ Mq := fun a ha => map_mono hAM ha
  have hAq : IsPGroup p Aq := (hA.map q).comap_subtype
  have hAr : Aq.map r ≤ componentOverlap (minimalParabolicMax S hP) K :=
    map_le_iff_le_comap.mpr (hpre ▸ hAqM)
  have hesc : ¬ normalizer (Aq : Set _) ≤ Mq := by
    apply normalizer_not_le_of_two_kernel r (linearSourceComparison_surjective S hP K)
      (rank_one_comparison_kernel_isTwoGroup S hP K hK hqK hc hm) Mq Aq hp hAq
    have hn := rank_one_sourceImage_escape hm hp (Aq.map r) (hAq.map r) hAr
    have hMr : Mq.map r ≤ componentOverlap (minimalParabolicMax S hP) K :=
      map_le_iff_le_comap.mpr (hpre ▸ le_rfl)
    exact fun hh => hn (hh.trans hMr)
  have hout : ¬ normalizer (A.map q : Set _) ≤ (minimalParabolicMax S hP).map q := by
    intro hn
    apply hesc
    intro a ha
    have hh := Aq.le_normalizer_map (actorImage K).subtype
      (mem_map_of_mem (actorImage K).subtype ha)
    have hmap : Aq.map (actorImage K).subtype = A.map q :=
      map_subgroupOf_eq_of_le (map_mono hAK)
    rw [hmap] at hh
    exact hn hh
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  exact normalizer_not_le_of_two_kernel q (QuotientGroup.mk'_surjective _) hk
    (minimalParabolicMax S hP) A hp hA hout

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
