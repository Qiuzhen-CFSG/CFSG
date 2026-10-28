module
public import Theory.GroupTheory.QuaternionPresentation
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Quaternion subgroups from two generators

If c has order 2m, d² = c^m, conjugation by d inverts c, and d is outside
⟨c⟩, then ⟨c,d⟩ has order 4m and is isomorphic to QuaternionGroup m.
The strict positivity of m rules out the infinite cyclic case.

The integer normal forms give exactly two cosets of the cyclic subgroup.
Its exact order supplies the cardinality required by QuaternionPresentation.
The generic normal-form and generator-subtype lemmas are also exposed for
existing dihedral and quasi-dihedral consumers; these statements were first
proved in the ABG presentation development and are independent of it.

This is the elementary quaternion presentation argument used in
Alperin–Brauer–Gorenstein II.1 Lemmas 2(v) and 3, article pp.9–10.
-/

namespace Subgroup
variable {G : Type*} [Group G]

/-- Move the involutory generator past an integer power of the cyclic generator. -/
public theorem move_zpow (a b : G) (k : ℕ)
    (hconj : b * a * b⁻¹ = a ^ k) (i : ℤ) :
    b * a ^ i = a ^ ((k : ℤ) * i) * b := by
  have h := congrArg (fun x : G => x ^ i) hconj
  rw [← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply, ← zpow_natCast, ← zpow_mul] at h
  calc
    b * a ^ i = (b * a ^ i * b⁻¹) * b := by group
    _ = a ^ ((k : ℤ) * i) * b := congrArg (· * b) h

/-- The two integer normal forms remain valid when the second generator's square
is an arbitrary integer power of the first generator. -/
public theorem square_normal_form_int (a b : G) (k : ℕ)
    (r : ℤ) (hb : b ^ 2 = a ^ r) (hconj : b * a * b⁻¹ = a ^ k)
    (x : G) (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    ∃ i : ℤ, x = a ^ i ∨ x = a ^ i * b := by
  have hbb : b * b = a ^ r := by simpa [pow_two] using hb
  have hbi : b⁻¹ = a ^ (-r) * b := by
    have hr := congrArg (fun x : G => x⁻¹ * b) hbb
    simpa [mul_inv_rev, zpow_neg, mul_assoc] using hr
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨1, Or.inl (by simp)⟩
    · exact ⟨0, Or.inr (by simp)⟩
  | one => exact ⟨0, Or.inl (by simp)⟩
  | mul x y _ _ hx hy =>
    rcases hx with ⟨i, rfl | rfl⟩ <;> rcases hy with ⟨j, rfl | rfl⟩
    · exact ⟨i + j, Or.inl (zpow_add a i j).symm⟩
    · exact ⟨i + j, Or.inr (by rw [zpow_add, mul_assoc])⟩
    · exact ⟨i + k * j, Or.inr (by rw [mul_assoc, move_zpow a b k hconj, ← mul_assoc, ← zpow_add])⟩
    · refine ⟨i + k * j + r, Or.inl ?_⟩
      calc
        (a ^ i * b) * (a ^ j * b) = a ^ i * (b * a ^ j) * b := by group
        _ = a ^ i * (a ^ ((k : ℤ) * j) * b) * b := by rw [move_zpow a b k hconj]
        _ = a ^ (i + (k : ℤ) * j + r) := by rw [mul_assoc, mul_assoc, hbb, ← zpow_add, ← zpow_add]; congr 1; omega
  | inv x _ hx =>
    rcases hx with ⟨i, rfl | rfl⟩
    · exact ⟨-i, Or.inl (zpow_neg a i).symm⟩
    · refine ⟨-r + (k : ℤ) * (-i), Or.inr ?_⟩
      rw [mul_inv_rev, hbi, ← zpow_neg, mul_assoc, move_zpow a b k hconj, ← mul_assoc, ← zpow_add]

/-- The two designated elements generate the subgroup they generate in the ambient group. -/
public theorem generated_subtype (a b : G) :
    Subgroup.closure ({(⟨a, Subgroup.subset_closure (by simp)⟩ : Subgroup.closure ({a,b}:Set G)),
      ⟨b, Subgroup.subset_closure (by simp)⟩} : Set (Subgroup.closure ({a,b}:Set G)))=⊤ := by
  convert Subgroup.closure_preimage_eq_top ({a,b}:Set G) using 2
  ext x
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subgroup.coe_subtype]
  constructor
  · rintro (rfl | rfl) <;> simp
  · rintro (h | h)
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

end Subgroup
namespace QuaternionGroup
variable {G : Type*} [Group G]
public theorem closure_equiv_of_relations {m : ℕ} (hm : 0 < m) (c d : G)
    (hc : orderOf c = 2 * m) (hsq : d ^ 2 = c ^ m)
    (hinv : d * c * d⁻¹ = c⁻¹) (hout : d ∉ Subgroup.zpowers c) :
    Nat.card (Subgroup.closure ({c,d} : Set G)) = 4 * m ∧
      Nonempty ((Subgroup.closure ({c,d} : Set G)) ≃* QuaternionGroup m) := by
  let U := Subgroup.closure ({c,d} : Set G)
  let c' : U := ⟨c, Subgroup.subset_closure (by simp)⟩
  let d' : U := ⟨d, Subgroup.subset_closure (by simp)⟩
  have hc' : orderOf c' = 2 * m := by
    rw [← orderOf_injective U.subtype U.subtype_injective]
    exact hc
  have hsq' : d' ^ 2 = c' ^ m := by apply Subtype.ext; exact hsq
  have hinv' : d' * c' * d'⁻¹ = c'⁻¹ := by apply Subtype.ext; exact hinv
  have hgen : Subgroup.closure ({c',d'} : Set U) = ⊤ :=
    Subgroup.generated_subtype c d
  have hout' : d' ∉ Subgroup.zpowers c' := by
    rintro ⟨i,hi⟩
    exact hout ⟨i, congrArg (fun x : U => (x : G)) hi⟩
  have hci : c'⁻¹ = c' ^ (2 * m - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (by omega), ← hc', pow_orderOf_eq_one]
  have hidx : (Subgroup.zpowers c').index = 2 := by
    apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
    refine ⟨d', hout', ?_⟩
    intro x
    have hx : x ∈ Subgroup.closure ({c',d'} : Set U) := by rw [hgen]; trivial
    obtain ⟨i, rfl | rfl⟩ := Subgroup.square_normal_form_int c' d'
      (2 * m - 1) m (by simpa using hsq') (hinv'.trans hci) x hx
    · right; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    · left
      have hdd : d' * d' = c' ^ m := by simpa [pow_two] using hsq'
      rw [mul_assoc, hdd]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _)
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
  have hcard : Nat.card U = 4 * m := by
    have ht := (Subgroup.zpowers c').card_mul_index
    rw [Nat.card_zpowers, hc', hidx] at ht
    omega
  exact ⟨hcard, QuaternionGroup.quaternionGroup_equiv_of_presentation hm
    c' d' hc' hsq' hinv' hgen hcard⟩

end QuaternionGroup
