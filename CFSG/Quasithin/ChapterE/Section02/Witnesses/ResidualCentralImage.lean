module
public import Theory.GroupTheory.PResidual.FixedNormalCenter
public import Theory.ElementaryAbelian.Basic
public import CFSG.Quasithin.ChapterB.Section06To07.Residual

/-!
# The original residual-fixed module in the maximal quotient

The source hypothesis that O²(M) centralizes V, together with normality of
V in the prescribed Sylow subgroup, makes V normal in M. Its nontrivial
image in H/J meets the center of the actual M-image nontrivially. The
central point stays in the image of the original V under the literal
quotient map, so centerless model Borels can be excluded directly.

Source: Aschbacher--Smith, E.2.17, first paragraph of the nonsolvable
reduction, printed p.230. No quotient classification is used here.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses
variable {H : Type*} [Group H] [Finite H]

theorem source_maximal_normalizes_of_residual_centralizes
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V : Subgroup H) (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    ChapterB.minimalParabolicMax T hP ≤ normalizer (V : Set H) := by
  let M := ChapterB.minimalParabolicMax T hP
  have hTM : (T : Subgroup H) ≤ M := (ChapterB.minimalParabolicMax_spec T hP).2
  have hTV : (T : Subgroup H) ≤ normalizer (V : Set H) :=
    (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have he := congrArg (Subgroup.map M.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTM))
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM,
    ←MonoidHom.range_eq_map,range_subtype] at he
  change M ≤ normalizer (V : Set H)
  rw [←he]
  exact sup_le (hres.trans (Subgroup.centralizer_le_normalizer _)) hTV

/-- The original residual-fixed module meets the original maximal center. -/
theorem source_maximal_center_point
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal) (hne : V ≠ ⊥)
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    ∃ v ∈ V, v ≠ 1 ∧ v ∈ (center (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype := by
  let M := ChapterB.minimalParabolicMax T hP
  have hTM : (T : Subgroup H) ≤ M := (ChapterB.minimalParabolicMax_spec T hP).2
  have hVM : V ≤ M := hVT.trans hTM
  let C := V.subgroupOf M
  let : C.Normal := (normal_subgroupOf_iff_le_normalizer hVM).mpr
    (source_maximal_normalizes_of_residual_centralizes T hP V hVT hvn hres)
  have hCne : C ≠ ⊥ := by
    intro he
    apply hne
    rw [←map_subgroupOf_eq_of_le hVM]
    rw [show V.subgroupOf M = ⊥ from he,Subgroup.map_bot]
  have hR : pResidual 2 M ≤ centralizer (C : Set M) := by
    intro r hr c hc
    exact Subtype.ext (mem_centralizer_iff.mp (hres (mem_map_of_mem M.subtype hr)) c hc)
  obtain ⟨v,hv,hvne,hvc⟩ := exists_nontrivial_center_mem_normal_of_residual_centralizes
    (T.subtype hTM) C (IsElementaryAbelian.isPGroup 2 V).comap_subtype hCne hR
  exact ⟨v,hv,fun he => hvne (Subtype.ext he),mem_map_of_mem M.subtype hvc⟩

theorem source_star_maximal_center_point
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
    ∃ v ∈ V.map q, v ≠ 1 ∧ v ∈
      (center ((ChapterB.minimalParabolicMax T hP).map q)).map
        ((ChapterB.minimalParabolicMax T hP).map q).subtype := by
  let M := ChapterB.minimalParabolicMax T hP
  exact exists_nontrivial_center_image_of_residual_centralizes M V
    (hVT.trans (ChapterB.minimalParabolicMax_spec T hP).2)
    (source_maximal_normalizes_of_residual_centralizes T hP V hVT hvn hres)
    (IsElementaryAbelian.isPGroup 2 V) hres
    (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))
    (by simpa only [QuotientGroup.ker_mk'] using hout)

theorem source_star_maximal_center_ne_bot
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    center ((ChapterB.minimalParabolicMax T hP).map
      (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) ≠ ⊥ := by
  obtain ⟨v,_,hv,hvc⟩ := source_star_maximal_center_point T hP V hVT hvn hout hres
  intro he
  rw [he,Subgroup.map_bot,mem_bot] at hvc
  exact hv hvc
end CFSG.Quasithin.ChapterE.Witnesses
