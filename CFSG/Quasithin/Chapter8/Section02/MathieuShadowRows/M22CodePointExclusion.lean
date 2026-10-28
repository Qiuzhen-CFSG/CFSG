module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.Complete
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCentralizerQuotient
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetResidual
/-!
# Excluding the original order-32 A₆ point image

Restrict the original Sylow and point residual to the involution
centralizer, then project by its full two-core. The solvable projection
kernel preserves the actual local C-component and its Sylow normalization.
The complete source carrier inspection excludes the resulting full A₆
section when its intrinsic two-core has order 32.

The caller supplies these two numerical and quotient conclusions from
the original point closure. Source: Aschbacher--Smith 8.2.13, printed
pp.722--723, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open Centralizer Chapter7.NormalizedSource.MathieuSextet
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- The original point-residual image cannot have the order-32 full A6
section in the genuine SQTK centralizer quotient. -/
theorem m22_point_quotient_exclusion
    (L : Subgroup G) (T : Sylow 2 G) (z : G)
    (hQ : IsSQTK KnownSimple.IsKnownSimple
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcomp : ((localResidual L z).subgroupOf
      (normalizer (L : Set G) ⊓ centralizer ({z} : Set G))).IsCComponent)
    (hcore : Nat.card (pCore 2 (pointResidualImage L z)) = 32)
    (hA6 : Nonempty ((pointResidualImage L z ⧸ pCore 2 (pointResidualImage L z)) ≃*
      alternatingGroup (Fin 6))) : False := by
  let C := centralizer ({z} : Set G)
  let R := localResidual L z
  let π := QuotientGroup.mk' (pCore 2 C)
  let S := T.subtype hTC
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
  have hRC : R ≤ C := (localResidual_le L z).trans inf_le_right
  have hRM : R ≤ normalizer (L : Set G) ⊓ C :=
    (localResidual_le L z).trans (inf_le_inf_right _ L.le_normalizer)
  have hlocal : R ∈ localCComponents (T : Subgroup G) :=
    hcomp.subgroupOf_of_le le_sup_left (sup_le hRM (le_inf hTL hTC))
  have hlocalC : R.subgroupOf C ∈ localCComponents S :=
    ChapterA.Section03.SourceEmbeddings.local_restrict hlocal hRC
  let : Group.IsSolvable π.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (pCore 2 C)).ker
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 C) := pCore_isPGroup.isNilpotent
    infer_instance
  have hlocalQ : (R.subgroupOf C).map π ∈ localCComponents P :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hlocalC π
  have hnormC : (S : Subgroup C) ≤ normalizer (R.subgroupOf C : Set C) := by
    rw [←subgroupOf_normalizer_eq hRC]
    exact comap_mono ((le_inf hTL hTC).trans (residual_normalized L z))
  have hnormQ : (P : Subgroup (C ⧸ pCore 2 C)) ≤
      normalizer ((R.subgroupOf C).map π : Set _) :=
    (map_mono hnormC).trans (le_normalizer_map π)
  exact Order32Six.no_local_order32_six hQ (pCore_quotient_pCore_eq_bot 2)
    P (pointResidualImage L z) hlocalQ hnormQ hcore hA6

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
