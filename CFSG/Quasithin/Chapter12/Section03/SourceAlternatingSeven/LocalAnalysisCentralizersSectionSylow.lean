module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowModelsTransport
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.NormalizerAction

/-!+# The literal section Sylow subgroup of a central point residual

A.4.2 gives the two-core of K T as a Sylow subgroup of the section
centralizer in N_G(K), where K=C_L(v)∞. Since v centralizes T, this
two-core lies in C_G(v). Restriction gives the Sylow statement for the
original section centralizer C_{C_G(v)}(K/O₂(K)). In the weight-six branch,
the common-core identity identifies this subgroup with O₂(LT).

Source: Aschbacher--Smith, 12.2.12(1) and 12.3.6, pp.799,809, using
A.4.2(4--5), p.57. The common-core identity and ambient component
rigidity are still required by the point-centralizer assembly owner
qt-d-1236-1238-point-centralizers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
namespace SylowNormalizer

include S in
/-- Section-Sylow placement for the actual perfect residual of a central point. -/
theorem pointResidual_section_sylow (v : V)
    (hv : (v : G) ∈ centralizer (T : Set G)) :
    ∃ R : Sylow 2 (twoSectionCentralizer (pointResidual L v)
        (centralizer ({(v : G)} : Set G))),
      (R : Subgroup _).map (twoSectionCentralizer (pointResidual L v)
        (centralizer ({(v : G)} : Set G))).subtype =
          (pointResidual L v ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let K := pointResidual L v
  let C := centralizer ({(v : G)} : Set G)
  have hTC : (T : Subgroup G) ≤ C := fun t ht =>
    mem_centralizer_singleton_iff.mpr (hv t ht)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    pointResidual_normalized S.chosen.sylow_normalizes_component hv
  have hp : IsPPerfect 2 K := by
    intro N hn hq
    let := hn
    by_contra hne
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (K ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  have hs : Chapter1.IsSylowIn 2 ((K ⊔ (T : Subgroup G)).pCoreIn 2)
      (twoSectionCentralizer K (normalizer (K : Set G))) :=
    sylow_core_sectionCentralizer T K hp hTK
  have hQT : (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hQ := (Chapter1.isSylowIn_iff.mp hs).2.1
  apply hs.restrict
  · intro q hq
    exact ⟨hTC (hQT hq),(hQ hq).2⟩
  · intro y hy
    exact ⟨hy.2.1,hy.2⟩

namespace Points
variable {E : S.NaturalCoordinates} (P : Points E)

/-- The common-core calculation removes the last local-group change from
the section-Sylow input to the weight-six ambient endgame. -/
theorem six_section_sylow_of_core_eq
    (hcore : (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 =
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    ∃ R : Sylow 2 (twoSectionCentralizer P.sixGroup
        (centralizer ({(P.six : G)} : Set G))),
      (R : Subgroup _).map (twoSectionCentralizer P.sixGroup
        (centralizer ({(P.six : G)} : Set G))).subtype =
          (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  simpa only [← hcore] using pointResidual_section_sylow (S := S) P.six P.six_central

end Points
end SylowNormalizer
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
