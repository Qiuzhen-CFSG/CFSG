module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.UnitaryCovers
public import Theory.SpecificGroups.SU3.FullTorusNormalizer.ScalarBorel

/-!
# Full unitary source escape including the scalar prime

The actual quasisimple component image admits the proved scalar SU₃ cover.
Its full torus preimage is cyclic, and its Weyl element escapes the marked
Borel. Odd-primary subgroups therefore have escaping normalizers even at
three. The final lift uses only the original two-core quotient, so it
retains the prescribed subgroup without any coprimality restriction at
the scalar kernel.

Source: Aschbacher–Smith E.2.2(2a) and 4.4.13(1), pp.215–216,623–624.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
open MarkedModels MarkedModels.DiagramHall ChapterB
open BenderSuzuki.MatrixGroups HermitianForm HermitianForm.UniversalCover
variable {X : Type*} [Group X] [Finite X]

/-- Escape in the actual component image modulo the original two-core,
including at the scalar prime three. -/
theorem unitary_actorImage_escape
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K)) {f : ℕ}
    (hm : UnitaryModel (minimalParabolicMax S hP) K f)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (A : Subgroup (actorImage K))
    (hA : IsPGroup p A)
    (hAM : A ≤ ((minimalParabolicMax S hP).map
      (QuotientGroup.mk' (pCore 2 X))).subgroupOf (actorImage K)) :
    ¬ normalizer (A : Set (actorImage K)) ≤ ((minimalParabolicMax S hP).map
      (QuotientGroup.mk' (pCore 2 X))).subgroupOf (actorImage K) := by
  obtain ⟨F,hfield,hfin,hchar,J,hJ,hf,hF,hconj,_,e,he⟩ := hm
  let := hfield
  let := hfin
  let := hchar
  let := hqK
  let : IsQuasisimple (actorImage K) :=
    IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hsub : (actorImage K).IsSubnormal :=
    hK.subnormal.map (QuotientGroup.mk'_surjective (pCore 2 X))
  have hcore : pCore 2 (actorImage K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hsub,pCore_quotient_pCore_eq_bot]
    exact (actorImage K).subtype.ker_eq_bot (actorImage K).subtype_injective
  let r := e.toMonoidHom.comp (linearSourceComparison S hP K)
  have hr : Function.Surjective r := e.surjective.comp (linearSourceComparison_surjective S hP K)
  obtain ⟨k,hks,hk⟩ := OddPartDescent.exists_lift_even J hf hF hconj
    (fun p hp hp3 => EvenKernelBound.LargePrimary.not_dvd_universal_kernel J hf hp hp3 hF hconj)
    (fun hodd => EvenKernelBound.ThreePrimary.not_nine_dvd_universal_kernel J hf hodd hF hconj)
    r hr hcore
  have hpre : (Theory.SpecificGroups.BenderBorel.unitaryBorel J hJ).comap r =
      ((minimalParabolicMax S hP).map (QuotientGroup.mk' (pCore 2 X))).subgroupOf
        (actorImage K) :=
    Inverted.comparison_borel_preimage S hP K e _ he
  rw [← hpre] at hAM ⊢
  exact Theory.SpecificGroups.UnitaryBorel.odd_normalizer_not_le_borel_preimage_of_scalar_lift
    J hJ r hr k hks hk hp A hA hAM

/-- The complete unitary source branch of normalizer escape for every
prescribed odd-primary subgroup of the actual maximal subgroup. -/
theorem unitary_original_escape_all_odd
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (K : Subgroup X)
    (hK : K.IsCComponent) (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hc : SingleClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hm : UnitaryModel (minimalParabolicMax S hP) K f)
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
  let Aq : Subgroup (actorImage K) := (A.map q).subgroupOf (actorImage K)
  have hAqK : A.map q ≤ actorImage K := map_mono hAK
  have hAqM : Aq ≤ ((minimalParabolicMax S hP).map q).subgroupOf (actorImage K) := by
    intro a ha
    exact map_mono hAM ha
  have hAq : IsPGroup p Aq := (hA.map q).comap_subtype
  have hesc := unitary_actorImage_escape S hP K hK hqK hm hp Aq hAq hAqM
  have hout : ¬ normalizer (A.map q : Set _) ≤ (minimalParabolicMax S hP).map q := by
    intro hn
    apply hesc
    intro a ha
    have hh := Aq.le_normalizer_map (actorImage K).subtype
      (mem_map_of_mem (actorImage K).subtype ha)
    have hmap : Aq.map (actorImage K).subtype = A.map q := map_subgroupOf_eq_of_le hAqK
    rw [hmap] at hh
    exact hn hh
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  exact Theory.GroupTheory.normalizer_not_le_of_two_kernel q
    (QuotientGroup.mk'_surjective _) hk (minimalParabolicMax S hP) A hp hA hout

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
