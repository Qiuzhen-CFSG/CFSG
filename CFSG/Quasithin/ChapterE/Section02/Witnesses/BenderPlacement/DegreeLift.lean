module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.MarkedLift
import all CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.OriginalModels
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Degree preservation in the original marked pair lift

The genuine lift through the maximal core preserves the chosen model degree,
in addition to the original elementary subgroup, conjugator and Borel marking.
This extension intentionally inspects the two internal witness constructors
only to publish their degree equations; no definition body is re-exposed.
The higher-rank source consumer uses this to retain its strict degree bound.

Source: Aschbacher--Smith E.2.9, printed pp.221--222, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H : Type*} [Group H] [Finite H]

theorem OriginalWitness.of_linear_degree {T : Sylow 2 H} {M V : Subgroup H} {n : ℕ}
    (w : LinearTwo.Witness T M V n) : (OriginalWitness.of_linear w).degree = w.degree := by rfl

theorem OriginalWitness.of_suzuki_degree {T : Sylow 2 H} {M V : Subgroup H} {m : ℕ}
    (w : SuzukiWitness T M V m) :
    (OriginalWitness.of_suzuki w).degree = 2*w.parameter+1 := by rfl

/-- Preserve the exact degree of the supplied witness through the literal lift. -/
theorem lift_original_witness_degree (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    {n : ℕ}
    (w : OriginalWitness
      (T.mapSurjective (QuotientGroup.mk'_surjective (ChapterB.minimalParabolicCore T hP)))
      ((ChapterB.minimalParabolicMax T hP).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))
      (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) n) :
    ∃ w' : OriginalWitness T (ChapterB.minimalParabolicMax T hP) V n,
      w'.degree = w.degree := by
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
  exact ⟨⟨w',w.degree,w.positive,w.degree_dvd,w.model.transport e hmap⟩,rfl⟩

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
