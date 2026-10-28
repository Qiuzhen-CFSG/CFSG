module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.FrattiniQuotient
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import CFSG.Quasithin.ChapterB.Section02.Baumann.Defs
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The odd Frattini kernel in the rank-one Baumann argument

The kernel of the natural action lies in the minimal-parabolic core. For a
perfect action image, Frattini nongeneration shows that the two-residual
supplements O₂, so the actual residual map transports the Frattini preimage.
In the solvable case B.6.8 identifies the core image with the Frattini subgroup
of the residual image instead. Both routes remove only a two-group kernel.
Source: Aschbacher–Smith B.6.10, printed p.117, applying B.6.8(2),(7).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
variable {G D : Type*} [Group G] [Finite G] [Group D]

public theorem coreImage_frattini (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤) :
    (minimalParabolicCore T hP).map (QuotientGroup.mk' (pCore 2 G)) =
      frattini (G ⧸ pCore 2 G) := by
  apply minimalParabolic_core_image_eq_frattini_of_source5 T hP
  exact (minimalParabolicTwoCoreSylowPremise_iff T hP).mpr
    (minimalParabolic_twoCore_sylow_core T hP)

public theorem residual_sup_twoCore_of_perfect_image
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker ≤ minimalParabolicCore T hP) (hD : IsPPerfect 2 D) :
    pResidual 2 G ⊔ pCore 2 G = ⊤ := by
  let L := pResidual 2 G
  let J := minimalParabolicCore T hP
  let Q := pCore 2 G
  let π := QuotientGroup.mk' Q
  have hLq : L.map q = ⊤ := by
    change (pResidual 2 G).map q = ⊤
    rw [map_pResidual_of_surjective 2 q hq, (pResidual_eq_top_iff 2 D).mpr hD]
  have hLJ : L ⊔ J = ⊤ := by
    have hh := congrArg (comap q) hLq
    rw [comap_map_eq, comap_top] at hh
    exact top_unique (hh.symm.le.trans (sup_le_sup_left hker L))
  have hLF : L.map π ⊔ frattini (G ⧸ Q) = ⊤ := by
    rw [← coreImage_frattini T hP, ← Subgroup.map_sup, hLJ,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)]
  have hLtop := frattini_nongenerating hLF
  have hh := congrArg (comap π) hLtop
  simpa only [comap_map_eq, π, QuotientGroup.ker_mk', comap_top, L, Q] using hh

private theorem frattini_lift
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (C : Subgroup G) (hCJ : C ≤ minimalParabolicCore T hP)
    (hLQ : pResidual 2 G ⊔ pCore 2 G = ⊤) :
    pResidual 2 G ⊓ C ≤ BaumannArgument.coreFrattini (pResidual 2 G) := by
  let L := pResidual 2 G
  let Q := pCore 2 G
  let π := QuotientGroup.mk' Q
  let f : L →* G ⧸ Q := π.comp L.subtype
  have hf : Function.Surjective f := by
    have hm : L.map π = ⊤ := by
      have hh := congrArg (map π) hLQ
      simpa only [Subgroup.map_sup, π, Q, L, QuotientGroup.map_mk'_self,sup_bot_eq,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective Q)] using hh
    intro y
    obtain ⟨x,hx,hxy⟩ := hm.symm ▸ mem_top y
    exact ⟨⟨x,hx⟩,hxy⟩
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = Q.subgroupOf L := by
      ext x
      exact QuotientGroup.eq_one_iff (x:G)
    rw [he]
    exact pCore_isPGroup.comap_subtype
  have htransport := f.comap_frattini_pCore_of_pKernel hf hk
  intro x hx
  refine mem_map.mpr ⟨⟨x,hx.1⟩,?_,rfl⟩
  rw [← htransport]
  have hxF : π x ∈ frattini (G ⧸ Q) := by
    rw [← coreImage_frattini T hP]
    exact mem_map_of_mem π (hCJ hx.2)
  exact frattini_le_comap_frattini_of_surjective
    (QuotientGroup.mk'_surjective (pCore 2 (G ⧸ Q))) hxF

/-- A Frattini containment in the literal residual image lifts through O₂. -/
public theorem residual_intersection_le_coreFrattini_of_image
    (C : Subgroup G)
    (hC : C.map (QuotientGroup.mk' (pCore 2 G)) ≤
      Stellmacher.frattiniAmbient ((pResidual 2 G).map
        (QuotientGroup.mk' (pCore 2 G)))) :
    pResidual 2 G ⊓ C ≤ BaumannArgument.coreFrattini (pResidual 2 G) := by
  let L := pResidual 2 G
  let Q := pCore 2 G
  let π := QuotientGroup.mk' Q
  let f := π.subgroupMap L
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = Q.subgroupOf L := by
      ext x
      change (⟨π x, mem_map_of_mem π x.property⟩ : L.map π) = 1 ↔ (x:G) ∈ Q
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff (x:G)
    rw [he]
    exact pCore_isPGroup.comap_subtype
  have htransport := f.comap_frattini_pCore_of_pKernel
    (π.subgroupMap_surjective L) hk
  intro x hx
  refine mem_map.mpr ⟨⟨x,hx.1⟩,?_,rfl⟩
  rw [← htransport]
  have hxF := hC (mem_map_of_mem π hx.2)
  obtain ⟨y,hy,he⟩ := hxF
  have hfy : f ⟨x,hx.1⟩ = y := Subtype.ext he.symm
  change QuotientGroup.mk' (pCore 2 (L.map π)) (f ⟨x,hx.1⟩) ∈ frattini ((L.map π) ⧸ pCore 2 (L.map π))
  rw [hfy]
  exact frattini_le_comap_frattini_of_surjective
    (QuotientGroup.mk'_surjective (pCore 2 (L.map π))) hy

public theorem residual_core_le_coreFrattini_of_solvable
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hs : Group.IsSolvable G) :
    pResidual 2 G ⊓ minimalParabolicCore T hP ≤
      BaumannArgument.coreFrattini (pResidual 2 G) := by
  obtain ⟨p,hp,ho,hr,hquot,hPhi,hstar,hir⟩ :=
    minimalParabolic_solvable_structure T hP hs
  apply residual_intersection_le_coreFrattini_of_image
  rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _), hr]
  exact hPhi.le

public theorem residual_kernel_le_coreFrattini_of_perfect_image
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (q : G →* D) (hq : Function.Surjective q)
    (hker : q.ker ≤ minimalParabolicCore T hP) (hD : IsPPerfect 2 D) :
    pResidual 2 G ⊓ q.ker ≤ BaumannArgument.coreFrattini (pResidual 2 G) :=
  frattini_lift T hP q.ker hker (residual_sup_twoCore_of_perfect_image T hP q hq hker hD)
end CFSG.Quasithin.ChapterB.RankOneBaumann
