module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Max2Bridge
public import Mathlib.Algebra.Group.Subgroup.Finite


open scoped IsMulCommutative

/-!
# A fourth-power bound from central involution relations

If a family commutes and has square one modulo a central involution,
its generated subgroup has exponent dividing four. Pass to the quotient
by that involution, prove exponent two by closure induction, and lift.
This is the structural part of the max2 normal-closure two-group proof.

Source motivation: GLS3 Table 5.3i, printed p.270. The concrete words come
from ATLAS `J4G1-max2W1`, documented in `TwoCoreCentralizer.Words`.
Neither the global J₄ order nor a local model identification is assumed.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl

lemma closure_pow_two {G : Type*} [Group G] {ι : Type*} (e : ι → G)
    (hs : ∀ i, e i ^ 2 = 1) (hc : ∀ i j, Commute (e i) (e j))
    {g : G} (hg : g ∈ Subgroup.closure (Set.range e)) : g ^ 2 = 1 := by
  have hcomm : IsMulCommutative (Subgroup.closure (Set.range e)) :=
    Subgroup.isMulCommutative_closure (by
      rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
      exact (hc i j).eq)
  induction hg using Subgroup.closure_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hs i
  | one => exact one_pow _
  | mul a b ha hb ia ib =>
    have hab : Commute a b := by
      exact congrArg Subtype.val (mul_comm
        (⟨a, ha⟩ : Subgroup.closure (Set.range e)) ⟨b, hb⟩)
    rw [hab.mul_pow, ia, ib, one_mul]
  | inv a ha ia => rw [inv_pow, ia, inv_one]

lemma closure_pow_four {G : Type*} [Group G] {ι : Type*} (t : G) (e : ι → G)
    (ht : t ∈ Subgroup.center G) (ht2 : t ^ 2 = 1)
    (hs : ∀ i, e i ^ 2 = 1 ∨ e i ^ 2 = t)
    (hc : ∀ i j, e i * e j = e j * e i ∨ e i * e j = e j * e i * t)
    {g : G} (hg : g ∈ Subgroup.closure (Set.range e)) : g ^ 4 = 1 := by
  let Z := Subgroup.zpowers t
  have hz : Z ≤ Subgroup.center G := Subgroup.zpowers_le.mpr ht
  let : Z.Normal := ⟨fun n hn x => by
    rw [(Subgroup.mem_center_iff.mp (hz hn)) x, mul_inv_cancel_right]
    exact hn⟩
  let q := QuotientGroup.mk' Z
  have hqt : q t = 1 := (QuotientGroup.eq_one_iff t).mpr (Subgroup.mem_zpowers t)
  have hqs : ∀ i, (q (e i)) ^ 2 = 1 := by
    intro i
    rw [← map_pow]
    rcases hs i with hi | hi <;> rw [hi]
    · exact map_one q
    · exact hqt
  have hqc : ∀ i j, Commute (q (e i)) (q (e j)) := by
    intro i j
    change q (e i) * q (e j) = q (e j) * q (e i)
    rw [← map_mul, ← map_mul]
    rcases hc i j with hij | hij
    · rw [hij]
    · rw [hij, map_mul, hqt, mul_one]
  have hqg : q g ∈ Subgroup.closure (Set.range (fun i => q (e i))) := by
    have hm : Subgroup.closure (Set.range e) ≤
        (Subgroup.closure (Set.range (fun i => q (e i)))).comap q := by
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨i, rfl⟩
      exact Subgroup.subset_closure (Set.mem_range_self i)
    exact hm hg
  have hg2 : g ^ 2 ∈ Z := (QuotientGroup.eq_one_iff _).mp (by
    change q (g ^ 2) = 1
    rw [map_pow]
    exact closure_pow_two _ hqs hqc hqg)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg2
  calc
    g ^ 4 = (g ^ 2) ^ 2 := pow_mul g 2 2
    _ = (t ^ k) ^ 2 := by rw [hk]
    _ = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul,
      zpow_natCast, ht2, one_zpow]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl
