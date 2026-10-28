module
public import CFSG.Quasithin.ChapterC.Section02.ThompsonNormalizer
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.OffenderSource

/-!
# The source Thompson normalizer inside the marked intersection

The seed-centralizer comparison identifies the star kernel with O₂(LR),
which lies in the actual radical R. Thompson heredity through this kernel
therefore lifts the normalizer of J(R)* exactly. Characteristic-normalizer
control gives its containment in the proper marked intersection M∩L.
The selected application constructs local radicality from its original data.

This proves the displayed (*) restriction used before the C.2.7 block and
parabolic cases. It does not assume or assert those classification cases.
Source: Aschbacher–Smith C.2.7, printed p.146; 15.4.20, p.1164.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
open SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

theorem source_star_thompson_normalizer_of_local_radical
    (h : Input d i j H U K) (L : Subgroup H) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) L)
    (hr : IsPRadical 2 (((sourceRadical d U).subgroupOf H).subgroupOf
      (L ⊔ (sourceRadical d U).subgroupOf H))) :
    let R := (sourceRadical d U).subgroupOf H
    let M := d.M₁.subgroupOf H
    starComponent L R ⊓ normalizer (starThompson L R : Set (Star L R)) ≤
      starIntersection L R M ∧ starIntersection L R M < starComponent L R := by
  let R := (sourceRadical d U).subgroupOf H
  let M := d.M₁.subgroupOf H
  let D := L ⊔ R
  have hk : starKernel L R = pCore 2 D :=
    (h.local_module_comparison L hc.normalized hr).2.2.2.2
  have hQR : pCore 2 D ≤ R.subgroupOf D :=
    pCore_le_of_pCore_normalizer_le _ hr.isPGroup hr.2.le
  have hcontrol : (R.subgroupOf D).characteristicNormalizerClosure ≤ M.subgroupOf D :=
    characteristicNormalizerClosure_subgroupOf_le le_sup_right hc.characteristic_control
  have hout : ¬ L.subgroupOf D ≤ M.subgroupOf D := by
    intro he
    apply hc.outside
    intro l hl
    exact he (show (⟨l,(show L ≤ D from le_sup_left) hl⟩ : D) ∈ L.subgroupOf D from hl)
  have hker : (starProjection L R).ker ≤ R.subgroupOf D := by
    change (QuotientGroup.mk' (starKernel L R)).ker ≤ _
    rw [QuotientGroup.ker_mk',hk]
    exact hQR
  have hf := ChapterC.thompson_image_intersection_control
    (R.subgroupOf D) (M.subgroupOf D) (L.subgroupOf D) hr.isPGroup hr.1
    hcontrol hout (starProjection L R) (QuotientGroup.mk'_surjective _) hker
  simpa only [starComponent,starThompson,starIntersection,starProjection,
    show L.subgroupOf D ⊓ M.subgroupOf D = (M ⊓ L).subgroupOf D by
      ext x; exact and_comm] using hf

theorem source_selected_thompson_normalizer
    (h : Input d i j H U K) (s : Selected H U K K₁ r) (κ : GroupClass.{u})
    (hc : ComponentHypotheses κ H ((sourceRadical d U).subgroupOf H)
      (d.M₁.subgroupOf H) (K₁.subgroupOf H)) :
    let L := K₁.subgroupOf H
    let R := (sourceRadical d U).subgroupOf H
    let M := d.M₁.subgroupOf H
    starComponent L R ⊓ normalizer (starThompson L R : Set (Star L R)) ≤
      starIntersection L R M ∧ starIntersection L R M < starComponent L R :=
  source_star_thompson_normalizer_of_local_radical h _ κ hc
    (source_local_radical h s hc.normalized)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly
