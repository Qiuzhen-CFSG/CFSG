module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.WreathAction
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.ElementaryResidualKernel
-- Internal continuation of the canonical core construction.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.SolvableCoordinates.ResidualElementary

/-!
# The original minimal-parabolic core is the Ω-orbit action kernel

The full source action has elementary cubic residual. B.6.8 therefore kills
the canonical core of its faithful centralizer quotient. Lifting through the
literal quotient proves J=C_H(U), where J is the original maximal-subgroup
core. This is the first assertion inside the proof of13.2.9; the further
assertion that this kernel is a two-group is deliberately a separate step.

Source: Aschbacher–Smith13.2.9, printedp.880.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside
variable {G : Type*} [Group G] [Finite G]

/-- The first genuine kernel identification in the proof of13.2.9. -/
theorem source_core_eq_omega_centralizer
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    let h := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
    ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) h.2.2.1 =
      centralizer ((omegaOrbit T H).subgroupOf H : Set H) := by
  let h := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  let U := (omegaOrbit T H).subgroupOf H
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let := hs
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let : IsElementaryAbelian 3 (pResidual 2 (H ⧸ C)) :=
    (source_solvable_wreath_omega_action d hH hB hZ hs).residual_elementary
  have hne : q.ker ≠ ⊤ := by
    rw [QuotientGroup.ker_mk']
    intro he
    apply h.2.2.2.2
    exact le_top.trans_eq he.symm
  exact (ChapterB.minimalParabolic_core_eq_kernel_of_elementary_residual
    (T.subtype hH.1.1.2) h.2.2.1 q (QuotientGroup.mk'_surjective C)
    hU.quotient_pCore_eq_bot hne inferInstance (p := 3)).trans (QuotientGroup.ker_mk' C)

omit [Finite G] in
private theorem source_maximal_eq_overlap
    {T : Sylow 2 G} {L H : Subgroup G}
    (_hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) :
    ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hp =
      (normalizer (L : Set G)).subgroupOf H := by
  let B := ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hp
  have hb := ChapterB.minimalParabolicMax_spec (T.subtype hH.1.1.2) hp
  have hm : B.map H.subtype < H := by
    apply lt_of_le_of_ne (map_subtype_le B)
    intro he
    apply hb.1.ne_top
    apply map_injective H.subtype_injective
    exact he.trans (by rw [← MonoidHom.range_eq_map,range_subtype])
  have ht : (T : Subgroup G) ≤ B.map H.subtype := by
    intro t ht
    exact ⟨⟨t,hH.1.1.2 ht⟩,hb.2 ht,rfl⟩
  have hBM := Chapter3.HStar.proper_overgroup_le T hH ht hm
  have hle : B ≤ (normalizer (L : Set G)).subgroupOf H :=
    fun _ hx => hBM (mem_map_of_mem H.subtype hx)
  by_contra hne
  have he := hb.1.2 _ (lt_of_le_of_ne hle hne)
  apply hH.1.2
  intro x hx
  have hh : (⟨x,hx⟩ : H) ∈ (normalizer (L : Set G)).subgroupOf H :=
    he.symm ▸ mem_top _
  exact hh

/-- The source's literal core of H∩N(L), rather than an unnamed canonical copy. -/
theorem source_overlap_core_eq_omega_centralizer
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    ((normalizer (L : Set G)).subgroupOf H).normalCore =
      centralizer ((omegaOrbit T H).subgroupOf H : Set H) := by
  let h := e23_hypotheses d.hypothesis.qtke T d.normalizes_L hH hB hZ
  have hm := source_maximal_eq_overlap d.normalizes_L hH h.2.2.1
  have he := source_core_eq_omega_centralizer d hH hB hZ hs
  change (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) h.2.2.1).normalCore = _ at he
  rw [hm] at he
  exact he

/-- The actual whole kernel lies inside the original overlap; used for X=O²(C_H(U)). -/
theorem source_omega_centralizer_le_local
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    (centralizer ((omegaOrbit T H).subgroupOf H : Set H)).map H.subtype ≤ normalizer (L : Set G) := by
  rw [← source_overlap_core_eq_omega_centralizer d hH hB hZ hs]
  rintro x ⟨x,hx,rfl⟩
  exact normalCore_le ((normalizer (L : Set G)).subgroupOf H) hx

end CFSG.Quasithin.Chapter13.Section02.A5Outside
