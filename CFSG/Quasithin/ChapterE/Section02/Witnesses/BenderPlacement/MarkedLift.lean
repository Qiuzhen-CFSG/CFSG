module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.OriginalModels
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Lifting the marked original quotient model through the maximal core

The genuine pair lift restores the original V and its internal conjugator,
Sylow intersection and two-closed normal core. Its restricted quotient map
pulls the original maximal intersection back exactly. Surjectivity maps that
intersection onto the star intersection, and the core-quotient equivalence
therefore transports the exact Borel image as well as the model and degree.

Source: Aschbacher–Smith E.2.9, printed pp.221–222. This module transports
already constructed witnesses; the Source descendant constructs its input.
-/

public section
noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H : Type*} [Group H] [Finite H]

noncomputable def QuotientModel.transport {I L : Type*} [Group I] [Group L]
    {A : Subgroup I} {B : Subgroup L} {d : ℕ}
    (w : QuotientModel B d) (e : (I ⧸ A.normalCore) ≃* (L ⧸ B.normalCore))
    (hB : (A.map (QuotientGroup.mk' A.normalCore)).map e.toMonoidHom =
      B.map (QuotientGroup.mk' B.normalCore)) : QuotientModel A d := by
  cases w with
  | dihedral hd p a hp hp2 ha f => exact .dihedral hd p a hp hp2 ha (e.trans f)
  | linear hd f hb =>
    refine .linear hd (e.trans f) ?_
    change (A.map (QuotientGroup.mk' A.normalCore)).map
      (f.toMonoidHom.comp e.toMonoidHom) = _
    rw [←Subgroup.map_map,hB,hb]
  | suzuki m hm hd f hb =>
    refine .suzuki m hm hd (e.trans f) ?_
    change ∃c, (A.map (QuotientGroup.mk' A.normalCore)).map
      (f.toMonoidHom.comp e.toMonoidHom) = _
    rw [←Subgroup.map_map,hB]
    exact hb

/-- Lift a marked quotient model along the genuine original pair lift. -/
theorem lift_original_witness (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    {n : ℕ}
    (w : OriginalWitness
      (T.mapSurjective (QuotientGroup.mk'_surjective (ChapterB.minimalParabolicCore T hP)))
      ((ChapterB.minimalParabolicMax T hP).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))
      (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) n) :
    Nonempty (OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let B := M.map q
  obtain ⟨w',r,hr,hrq,e,he⟩ := QuotientLift.lift_pair T hP V hVT hn hVcore w.pair
  have hMpre : B.comap q = M := by
    rw [comap_map_eq,QuotientGroup.ker_mk']
    exact sup_eq_left.mpr (normalCore_le M)
  have hApre : (B.subgroupOf w.pair.subgroup).comap r = M.subgroupOf w'.subgroup := by
    ext x
    change (r x : H ⧸ J) ∈ B ↔ (x : H) ∈ M
    rw [hrq]
    exact SetLike.ext_iff.mp hMpre (x : H)
  have hAmap : (M.subgroupOf w'.subgroup).map r = B.subgroupOf w.pair.subgroup := by
    rw [←hApre,map_comap_eq_self_of_surjective hr]
  have hmap : ((M.subgroupOf w'.subgroup).map
        (QuotientGroup.mk' (M.subgroupOf w'.subgroup).normalCore)).map e.toMonoidHom =
      (B.subgroupOf w.pair.subgroup).map
        (QuotientGroup.mk' (B.subgroupOf w.pair.subgroup).normalCore) := by
    rw [Subgroup.map_map]
    have hh : e.toMonoidHom.comp (QuotientGroup.mk' (M.subgroupOf w'.subgroup).normalCore) =
        (QuotientGroup.mk' (B.subgroupOf w.pair.subgroup).normalCore).comp r := by
      apply MonoidHom.ext
      intro x
      exact he x
    rw [hh,←Subgroup.map_map,hAmap]
  exact ⟨⟨w',w.degree,w.positive,w.degree_dvd,w.model.transport e hmap⟩⟩



end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
