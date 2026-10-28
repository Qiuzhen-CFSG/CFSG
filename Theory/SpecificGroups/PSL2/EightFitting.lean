module
public import Theory.SpecificGroups.PSL2.BinaryOuter
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.Commutator.PerfectSmallIndex
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import GorensteinWalter.SL2ProjectiveCover
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Perfect sections in an actor with generalized Fitting subgroup SL₂(8)

The generalized Fitting subgroup is centerless and has solvable outer
group. Every perfect subgroup therefore lies inside it. A subgroup whose
two-core quotient has order at least 168 has index at most three in this
perfect group of order 504, so it is the whole subgroup. Neither 168 nor
20160 can then be its two-core quotient order: the former would leave a
two-core of order three.

This excludes the actual G.11.2(11) row in Aschbacher--Smith 12.9.4,
printed p.859, using the original point-residual quotient.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.PSL2.EightFitting
local notation "SL8" => Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 3)

private theorem card_model : Nat.card SL8 = 504 := by
  rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
    GaloisField.card 2 3 (by decide)]
  rfl

/-- A perfect subgroup of a group with generalized Fitting subgroup SL₂(8)
cannot have two-core quotient of order 168 or 20160. -/
theorem perfect_core_card_excluded {D : Type*} [_root_.Group D] [Finite D]
    (e : generalizedFitting D ≃* SL8) (B : Subgroup D) [_root_.Group.IsPerfect B]
    (hc : Nat.card (B ⧸ pCore 2 B) = 168 ∨ Nat.card (B ⧸ pCore 2 B) = 20160) : False := by
  let H := generalizedFitting D
  have hZ : center H = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hz : e x ∈ center SL8 := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z,rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx z)
    rw [Theory.PSL2.sl2_center_eq_bot,mem_bot] at hz
    exact e.injective (hz.trans e.map_one.symm)
  have hC : centralizer (H : Set D) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxH := centralizer_generalizedFitting_le D hx
    have hz : (⟨x,hxH⟩ : H) ∈ center H := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
    rw [hZ,mem_bot] at hz
    exact congrArg Subtype.val hz
  let : _root_.Group.IsSolvable (MulAut.Outer H) :=
    binary_outer_isSolvable_of_mulEquiv (GaloisField 2 3)
      (e.trans (sl2QuotientEquiv (GaloisField 2 3)))
  let : _root_.Group.IsSolvable (D ⧸ H) := quotient_isSolvable_of_centralizer_eq_bot H hC
  have hBH : B ≤ H := le_of_isPerfect_of_solvable_quotient B H
  have hH : Nat.card H = 504 := (Nat.card_congr e.toEquiv).trans card_model
  let : _root_.Group.IsPerfect SL8 := GorensteinWalter.sl2_isPerfect_of_card_gt_three
    (GaloisField 2 3) (by rw [GaloisField.card 2 3 (by decide)]; decide)
  let : _root_.Group.IsPerfect H := _root_.Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hBge : 168 ≤ Nat.card B := by
    have hh := Nat.le_of_dvd (Nat.card_pos (α := B)) (card_quotient_dvd_card (pCore 2 B))
    rcases hc with hc | hc <;> rw [hc] at hh <;> omega
  have hcard : Nat.card (B.subgroupOf H) = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv
  have hi : (B.subgroupOf H).index ≤ 4 := by
    have hh := (B.subgroupOf H).card_mul_index
    rw [hcard,hH] at hh
    nlinarith
  have htop : B.subgroupOf H = ⊤ := top_le_iff.mp
    (le_of_isPerfect_of_index_le_four ⊤ _ hi)
  have hBcard : Nat.card B = 504 := by
    rw [←hcard,htop,card_top,hH]
  have hm := card_eq_card_quotient_mul_card_subgroup (pCore 2 B)
  rw [hBcard] at hm
  rcases hc with hc | hc
  · rw [hc] at hm
    have h3 : 3 ∣ Nat.card (pCore 2 B) := by omega
    obtain ⟨k,hk⟩ := (pCore_isPGroup : IsPGroup 2 (pCore 2 B)).exists_card_eq
    rw [hk] at h3
    exact (by decide : ¬ 3 ∣ 2) ((Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3)) h3)
  · rw [hc] at hm
    have hp := Nat.card_pos (α := pCore 2 B)
    omega

end Theory.PSL2.EightFitting
