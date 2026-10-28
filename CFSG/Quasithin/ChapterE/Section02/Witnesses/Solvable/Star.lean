module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Solvable.CoreFree
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The actual solvable witness in the star quotient

The genuine B.6.8 structure of `H/J` supplies an elementary odd residual
disjoint from the marked maximal subgroup. Its action on the nontrivial
image of `V` cannot be trivial: otherwise that image would lie in the
trivial two-core. The core-free construction therefore supplies the actual
E.2.7 witness with its original quotient maps and Sylow subgroup.

Source: Aschbacher–Smith, E.2.9, printed pp.221–222.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterE.Witnesses.Solvable
open Subgroup ChapterB
variable {H : Type*} [Group H] [Finite H]

theorem solvable_star_witness (T : Sylow 2 H)
    (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hout : ¬ V ≤ minimalParabolicCore T hP) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nonempty
      (CoreFreeWitness
        ((minimalParabolicMax T hP).map (QuotientGroup.mk' (minimalParabolicCore T hP)))
        (V.map (QuotientGroup.mk' (minimalParabolicCore T hP))) p) := by
  let M := minimalParabolicMax T hP
  let J := minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  have hq := QuotientGroup.mk'_surjective J
  let S := T.mapSurjective hq
  let W := V.map q
  let B := M.map q
  have hWB : W ≤ B := map_mono (hVT.trans (minimalParabolicMax_spec T hP).2)
  have hWS : W ≤ (S : Subgroup (H ⧸ J)) := map_mono hVT
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hWnormal : (W.subgroupOf (S : Subgroup (H ⧸ J))).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hWS).mpr
    exact (map_mono ((normal_subgroupOf_iff_le_normalizer hVT).mp hn)).trans
      (V.le_normalizer_map q)
  have hWne : W ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff (f := q) (H := V)).mp he
    rw [QuotientGroup.ker_mk'] at hh
    exact hout hh
  have hcore : pCore 2 (H ⧸ J) = ⊥ := by
    have hCB : pCore 2 (H ⧸ J) ≤ B :=
      (pCore_isPGroup.le_sylow_of_normal S).trans
        (map_mono (minimalParabolicMax_spec T hP).2)
    have hpre : (pCore 2 (H ⧸ J)).comap q ≤ J := by
      change (pCore 2 (H ⧸ J)).comap q ≤ M.normalCore
      apply normal_le_normalCore.mpr
      have hh := comap_mono (f := q) hCB
      simpa only [B,q,comap_map_eq,QuotientGroup.ker_mk',
        sup_eq_left.mpr (show J ≤ M from normalCore_le M)] using hh
    have hh := map_mono (f := q) hpre
    rw [map_comap_eq_self_of_surjective hq] at hh
    exact bot_unique (hh.trans (by simp [q]))
  have hmove := residual_moves_elementary S W hWS hWnormal hcore hWne
  obtain ⟨p,hp,ho,he,_,hd⟩ := minimalParabolic_solvable_star_structure T hP hs
  let : Fact p.Prime := ⟨hp⟩
  let := he
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    exact ho.not_two_dvd_nat (dvd_refl 2)
  refine ⟨p,hp,hp2,?_⟩
  exact coreFreeWitness_of_moved_prime_group hp2 (pResidual 2 (H ⧸ J)) B W
    (IsElementaryAbelian.isPGroup p _) hWB (disjoint_iff.mpr hd) hmove
end CFSG.Quasithin.ChapterE.Witnesses.Solvable
end
