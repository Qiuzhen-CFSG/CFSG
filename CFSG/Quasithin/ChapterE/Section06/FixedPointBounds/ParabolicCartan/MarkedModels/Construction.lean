module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Hall
public import Theory.GroupTheory.Hall.Existence
public import Mathlib.Algebra.Group.PUnit

/-!
# Hall containment and the remaining model obligation

Hall's theorem puts a cyclic subgroup of odd order inside an odd Hall
subgroup of the maximal overgroup. The common Hall arithmetic then supplies
permutation with the original Sylow subgroup. Thus the outstanding marked
model output is precisely maximal solvability, Hall abelianness, and the
normalizer factorization; `HallControl` names this output for the three
independent model branches. It is not an earlier-source assumption and is
not claimed to follow from E.2.2 by a record projection.

The source assembly remains conditional until all three model branches
construct `HallControl`. The cyclic subgroup is supplied independently by
`MarkedModels.Cyclic`, with all component and quotient markings retained.
Source: Aschbacher--Smith, E.3.37, E.6.27 and 4.4.13, pp.239, 257, 623--624.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open ChapterB
universe u
variable {X : Type u} [Group X] [Finite X]

/-- Remaining output of the marked-model calculations. This is not an
earlier-source premise: the three branch owners must construct it from
E.2.2's actual models and central-extension clauses. -/
structure HallControl (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) : Prop where
  solvable : Group.IsSolvable (minimalParabolicMax S hP)
  abelian : ∀ Y : Subgroup X, Y ≤ minimalParabolicMax S hP →
    IsHallSubgroup oddPrimes (Y.subgroupOf (minimalParabolicMax S hP)) →
    IsMulCommutative Y
  frattini : ∀ Y : Subgroup X, Y ≤ minimalParabolicMax S hP →
    IsHallSubgroup oddPrimes (Y.subgroupOf (minimalParabolicMax S hP)) →
    ∃ Q : Subgroup X, Y ≤ normalizer (Q : Set X) ∧
      (S : Set X) = (Q : Set X) *
        ((S : Subgroup X) ⊓ normalizer (Y : Set X) : Set X)

/-- Hall's theorem places the already constructed cyclic group in an odd Hall
subgroup. The marked-model output then supplies abelianness and factorization. -/
theorem intrinsic_of_cyclic_and_hallControl (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) {n : ℕ} (hn : 0 < n)
    (hc : HallControl S hP)
    (hcyc : ∃ B : Subgroup X, B ≤ minimalParabolicMax S hP ∧
      IsCyclic B ∧ Nat.card B = 2 ^ n - 1) :
    Nonempty (IntrinsicHallCartanData S hP n) := by
  obtain ⟨B, hBM, hBcyc, hBcard⟩ := hcyc
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
    (hc.abelian YX hYX hYXhall) hBYX hBcyc hBcard hc.solvable hQ hfrat⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
