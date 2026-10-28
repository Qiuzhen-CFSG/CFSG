module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.MovingFirst

/-!
# Counting the remaining fixed factor

The marked second quotient and the core commutator row each have order 64.
Their indices give [K : K intersect hatV] = 4096. A bound of 4096 for the
literal index [K : Vcirc] then forces the entire residual fixed factor
into Vcirc, hence into H. The core center is U joined H and has order 32.

The moving-index bound remains an explicit source prerequisite; this is
not the complete (4.5) theorem from Earlier alone.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5)(iii)--(iv) and
(4.5.4)(iii)--(iv), printed pp.895,898--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open Higher
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

theorem core_first_relIndex_eq_fourThousandNinetySix (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (hatV R (alpha R) (p.walk.getVert 6)).relIndex (core R (alpha R)) = 4096 := by
  let K := core R (alpha R)
  let A := hatV R (alpha R) (p.walk.getVert 6)
  let B := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let Z₀ := Z R (alpha R)
  let := finite_stabilizer R (alpha R)
  obtain ⟨s⟩ := Quotients.SecondLayer.OrbitSource.marked_pair common earlier p
  let : Finite B := Finite.of_injective (inclusion s.local_group) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion s.lower_le) (inclusion_injective _)
  have hAB : A ≤ B := s.lower_le
  have hZA : Z₀ ≤ A := by
    dsimp only [Z₀,A]
    rw [(Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq]
    exact le_sup_right
  have hABcard : A.relIndex B = 64 := by
    have hi : s.quotient.ker.index = 64 := by
      rw [index_ker,s.quotient.range_eq_top_of_surjective s.onto,card_top]
      change Nat.card ((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) = 64
      simp only [Nat.card_prod,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
      norm_num
    rwa [s.kernel] at hi
  have hBK : B.relIndex K = 64 := by
    have he := first_centralizer_relIndex_eq_sixtyFour common earlier p
    rw [first_centralizer_eq_second common earlier p,inf_relIndex_left] at he
    exact he
  have hBKZ : B ≤ K ⊔ Z₀ := second_le_core_sup_Z common earlier p
  have hAK : K ⊔ A = K ⊔ Z₀ := by
    apply le_antisymm (sup_le le_sup_left (hAB.trans hBKZ))
    exact sup_le_sup_left hZA K
  have hBK' : K ⊔ B = K ⊔ Z₀ := by
    apply le_antisymm (sup_le le_sup_left hBKZ)
    exact sup_le_sup_left (hZA.trans hAB) K
  have hKA : A ≤ normalizer K :=
    (hAB.trans s.local_group).trans (DistanceTwo.core_normalized _)
  have hKB : B ≤ normalizer K := s.local_group.trans (DistanceTwo.core_normalized _)
  have ht := relIndex_mul_relIndex A B (K ⊔ Z₀) hAB hBKZ
  rw [hABcard,← hBK',relIndex_sup_of_normalizes K B hKB] at ht
  rw [hBK,hBK',← hAK,relIndex_sup_of_normalizes K A hKA] at ht
  exact ht.symm

theorem core_fixedFactor_eq_H_of_moving_index_bound
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (hbound : (Vcirc R (alpha R)).relIndex (core R (alpha R)) ≤ 4096) :
    core R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) =
      H R (alpha R) := by
  obtain ⟨p⟩ := Early.sourcePath_nonempty source common earlier (alpha R) rfl
  let K := core R (alpha R)
  let A := hatV R (alpha R) (p.walk.getVert 6)
  let D := Vcirc R (alpha R)
  have hDA : D ≤ A := by
    dsimp only [D,A]
    rw [(Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq]
    exact le_sup_left
  have hDK : D ≤ K := Vcirc_le_core rfl common.large_distance
  have ht := relIndex_mul_relIndex D (K ⊓ A) K (le_inf hDK hDA) inf_le_left
  rw [inf_relIndex_left,core_first_relIndex_eq_fourThousandNinetySix common earlier p] at ht
  have hindex : D.relIndex (K ⊓ A) = 1 := by
    change D.relIndex K ≤ 4096 at hbound
    have hn : D.relIndex (K ⊓ A) ≠ 0 := by
      let : Finite K := DistanceTwo.finite_core (alpha R)
      let : Finite (K ⊓ A : Subgroup (FreeAmalgam R)) :=
        Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
      exact index_ne_zero_of_finite
    omega
  have hle : K ⊓ A ≤ D := relIndex_eq_one.mp hindex
  have hZA : Z R (alpha R) ≤ A := by
    dsimp only [A]
    rw [(Early.Orbit.Source.Complete.sourceOrbitFacts common earlier p).hatV_eq]
    exact le_sup_right
  apply le_antisymm ?_ (earlier.factor_inclusions common).1
  rw [← moving_fixedFactor_eq_H common earlier p]
  exact le_inf ((le_inf inf_le_left ((core_fixedFactor_le_Z common earlier).trans hZA)).trans hle)
    inf_le_right
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

theorem core_center_eq_U_sup_H_of_moving_index_bound
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (hbound : (Vcirc R (alpha R)).relIndex (core R (alpha R)) ≤ 4096) :
    (center (core R (alpha R))).map (core R (alpha R)).subtype =
      U R (alpha R) ⊔ H R (alpha R) := by
  rw [core_center_eq_U_sup_fixedFactor common earlier,
    core_fixedFactor_eq_H_of_moving_index_bound common earlier hbound]

theorem core_center_card_of_moving_index_bound
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (hbound : (Vcirc R (alpha R)).relIndex (core R (alpha R)) ≤ 4096) :
    Nat.card (center (core R (alpha R))) = 32 := by
  have hH : Nat.card (H R (alpha R)) = 4 := Nat.le_antisymm
    (Early.H_card_le_four common earlier rfl)
    (Early.First.Layer.H_card_lower common earlier (alpha R) rfl)
  rw [core_center_card_eq_eight_mul_fixedFactor common earlier,
    core_fixedFactor_eq_H_of_moving_index_bound common earlier hbound,hH]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
