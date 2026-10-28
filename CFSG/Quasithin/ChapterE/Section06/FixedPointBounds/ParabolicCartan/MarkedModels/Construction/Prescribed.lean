module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Construction
/-!
# Retaining the prescribed cyclic subgroup in the Hall witness

Hall containment constructs the complete intrinsic witness while preserving
its supplied cyclic subgroup exactly. Thus the subgroup with the proved
normalizer-escape property is also the subgroup whose faithfulness is tested.
Source: Aschbacher–Smith E.3.37 and E.6.27, pp.239,257.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open ChapterB
universe u
variable {X : Type u} [Group X] [Finite X]
theorem intrinsic_with_prescribed_cyclic (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) {n : ℕ} (hn : 0 < n)
    (hc : HallControl S hP)
    (B : Subgroup X) (hBM : B ≤ minimalParabolicMax S hP)
    (hBcyc : IsCyclic B) (hBcard : Nat.card B = 2 ^ n - 1) :
    ∃ d : IntrinsicHallCartanData S hP n, d.witness.cyclicGroup = B := by
  let M := minimalParabolicMax S hP
  let _ : MulDistribMulAction Unit M := {
    smul _ x := x
    one_smul _ := rfl
    mul_smul _ _ _ := rfl
    smul_one _ := rfl
    smul_mul _ _ _ := rfl }
  have hodd : Odd (Nat.card B) := by
    rw [hBcard]
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) (even_two.pow_of_ne_zero (by omega)) odd_one
  have hpi : IsPiSubgroup oddPrimes (B.subgroupOf M) := by
    intro p hp
    change p.val ≠ 2
    intro he
    have hdiv : 2 ∣ Nat.card B := by
      simpa only [he, Nat.card_congr (subgroupOfEquivOfLe (show B ≤ M from hBM)).toEquiv] using hp
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)
  have hinv : IsInvariant Unit M (B.subgroupOf M) := ⟨fun _ _ => Iff.rfl⟩
  obtain ⟨Y, hYhall, _, hBY⟩ := exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (G := M) (A := Unit) hc.solvable (by simp) oddPrimes (B.subgroupOf M) hpi hinv
  let YX := Y.map M.subtype
  have hYX : YX ≤ M := map_subtype_le Y
  have hYXhall : IsHallSubgroup oddPrimes (YX.subgroupOf M) := by
    simpa only [YX, subgroupOf, comap_map_eq_self_of_injective M.subtype_injective] using hYhall
  have hBYX : B ≤ YX := by
    have hh := map_mono (f := M.subtype) hBY
    simpa only [map_subgroupOf_eq_of_le (show B ≤ M from hBM)] using hh
  obtain ⟨Q, hQ, hfrat⟩ := hc.frattini YX hYX hYXhall
  exact ⟨intrinsicOfHall S hP n YX B Q hYX hYXhall
    (hc.abelian YX hYX hYXhall) hBYX hBcyc hBcard hc.solvable hQ hfrat,rfl⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
