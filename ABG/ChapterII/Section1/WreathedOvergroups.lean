module
public import ABG.ChapterII.Section1.WreathedMaximalQuaternion
public import ABG.ChapterII.Section1.WreathedCenter
public import Theory.GroupTheory.CyclicTwoSubgroups

/-!
# Proper overgroups of the quaternion subgroup

ABG Chapter II §1 Lemma 2(xi), article p.10: if `Y < X < S`, then
`X = Y Z(X)` and `T ≤ X`. The source's strict containment `Y < X` is
essential for the second conclusion.

Normality of `Y` and `S = ⟨Y,sz⟩` express `X` as the join of `Y` with
its intersection with `⟨sz⟩`. The cyclic two-group subgroup calculation
makes that intersection `⟨(sz)^(2^k)⟩`. Properness excludes `k=0`, so its
generator is a power of the central element `u=(sz)^2`, proving the central
product expression. Strict containment excludes `k≥n`, since
`(sz)^(2^n)=x∈Y`. Thus `X` contains `u^(2^(n-2))`; together with the same
power of `r`, the identity `u*r=s²` yields `x₂` and hence all of `T`.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : ABG.Wreathed.Presentation S n)

private theorem overgroup_cyclic_supplement (hN : P.Y.Normal)
    (X : Subgroup S) (hYX : P.Y ≤ X) :
    ∃ k ≤ n + 1, X = P.Y ⊔ Subgroup.zpowers ((P.s * P.z) ^ (2 ^ k)) := by
  let := hN
  let v := P.s * P.z
  have hv : v ^ (2 ^ (n + 1)) = 1 := by
    rw [pow_succ, Nat.mul_comm, pow_mul, P.sz_sq]
    exact (show Commute P.s P.t from P.commute).mul_pow (2 ^ n) |>.trans (by rw [P.s_pow, P.t_pow, one_mul])
  obtain ⟨k, hk, he⟩ := Subgroup.eq_zpowers_two_pow_of_le hv (X ⊓ Subgroup.zpowers v) inf_le_right
  refine ⟨k, hk, ?_⟩
  rw [← he]
  apply le_antisymm
  · intro a ha
    have hatop : a ∈ P.Y ⊔ Subgroup.zpowers v := by rw [P.generator_change.2]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hatop
    exact Subgroup.mul_mem_sup hy ⟨by simpa using X.mul_mem (X.inv_mem (hYX hy)) ha, hz⟩
  · exact sup_le hYX inf_le_left

public theorem proper_overgroup
    (X : Subgroup S) (hX : X < ⊤) (hYX : P.Y < X) :
    X = P.Y ⊔ (Subgroup.center X).map X.subtype ∧ P.T ≤ X := by
  have hN := P.quaternion_subgroup.2.2
  have huc := P.u_mem_center
  obtain ⟨k, hkn, he⟩ := P.overgroup_cyclic_supplement hN X hYX.le
  have hk0 : 0 < k := by
    by_contra! hh
    have hk : k = 0 := by omega
    have hh := he
    rw [hk, pow_zero, pow_one, P.generator_change.2] at hh
    exact hX.ne hh
  have hvX : (P.s * P.z) ^ (2 ^ k) ∈ X := by
    rw [he]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hvu : (P.s * P.z) ^ (2 ^ k) = P.u ^ (2 ^ (k - 1)) := by
    have hk : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk, pow_succ, Nat.mul_comm, pow_mul, P.sz_sq]
  have hvcent : (P.s * P.z) ^ (2 ^ k) ∈ Subgroup.center S := by
    rw [hvu]
    exact (Subgroup.center S).pow_mem huc _
  constructor
  · apply le_antisymm
    · nth_rw 1 [he]
      apply sup_le le_sup_left
      apply Subgroup.zpowers_le_of_mem
      apply Subgroup.mem_sup_right
      refine ⟨⟨_, hvX⟩, ?_, rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro a
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp hvcent a
    · apply sup_le hYX.le
      exact Subgroup.map_subtype_le _
  · have hrY : P.r ∈ P.Y := Subgroup.subset_closure (by simp)
    have hxY : P.x ∈ P.Y := P.r_half ▸ P.Y.pow_mem hrY _
    have hvn : (P.s * P.z) ^ (2 ^ n) = P.x := by
      have hn : n = (n - 1) + 1 := by have := P.height; omega
      conv_lhs => arg 2; rw [hn, pow_succ, Nat.mul_comm]
      rw [pow_mul, P.sz_sq]
      rfl
    have hkn' : k < n := by
      by_contra! hn
      have hvY : (P.s * P.z) ^ (2 ^ k) ∈ P.Y := by
        obtain ⟨l, hl⟩ := Nat.pow_dvd_pow 2 hn
        rw [hl, pow_mul, hvn]
        exact P.Y.pow_mem hxY l
      have hXY : X ≤ P.Y := by
        rw [he]
        exact sup_le le_rfl (Subgroup.zpowers_le_of_mem hvY)
      exact hYX.not_ge hXY
    have huX : P.u ^ (2 ^ (n - 2)) ∈ X := by
      have hv : (P.s * P.z) ^ (2 ^ (n - 1)) ∈ X := by
        obtain ⟨l, hl⟩ := Nat.pow_dvd_pow 2 (show k ≤ n - 1 by omega)
        rw [hl, pow_mul]
        exact X.pow_mem hvX l
      have hn : n - 1 = (n - 2) + 1 := by have := P.height; omega
      rwa [hn, pow_succ, Nat.mul_comm, pow_mul, P.sz_sq] at hv
    have hx2X : P.x₂ ∈ X := by
      have hcomm : Commute P.u P.r := (Subgroup.mem_center_iff.mp huc P.r).symm
      have hh := X.mul_mem huX (X.pow_mem (hYX.le hrY) (2 ^ (n - 2)))
      rw [← hcomm.mul_pow, P.u_mul_r, ← pow_mul] at hh
      have heq : 2 * 2 ^ (n - 2) = 2 ^ (n - 1) := by
        have hn : n - 1 = (n - 2) + 1 := by have := P.height; omega
        rw [hn, pow_succ, Nat.mul_comm]
      simpa only [heq, x₂] using hh
    have hxX := hYX.le hxY
    have hx3X : P.x₃ ∈ X := by
      have hh := X.mul_mem (X.inv_mem hx2X) hxX
      simpa only [P.x_eq_x₂_mul_x₃, inv_mul_cancel_left] using hh
    apply (Subgroup.closure_le X).2
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hxX
    · exact hx2X
    · exact hx3X
end ABG.Wreathed.Presentation
