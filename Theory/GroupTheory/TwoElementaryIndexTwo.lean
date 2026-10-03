module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Index

/-!
# Two elementary abelian subgroups of index two

Let A and B be distinct elementary abelian two-subgroups of index two in a
finite group G. If G is not elementary abelian, every elementary abelian
two-subgroup of G is contained in A or B. In particular, these two subgroups
are the only maximal elementary abelian two-subgroups.

The main reduction shows that every involution belongs to A or B. Otherwise,
fix an involution x outside both and choose a in A outside B. Then xa lies
in B, so elements of A ∩ B commute with x = (xa)a⁻¹. Every other element
outside A and B differs from x by an element of this intersection, by the
two index-two coset calculations. It therefore also squares to one. Elements
inside A or B already square to one, which makes G elementary abelian and
contradicts the hypothesis. Finally, a subgroup contained in the union of
two subgroups is contained in one of them.

This is the elementary index-two recognition used in Stellmacher,
*Pushing up*, Arch. Math. 46 (1986), (3.4)(c), journal p.16, in the case
p = 2 and n = 1. The theorem is independent of the graph and pushing-up
hypotheses; the source application establishes these finite-group inputs.
-/

namespace Subgroup
open scoped IsMulCommutative

private theorem elementary_of_all_square_one
    {G : Type*} [Group G] (hsq : ∀ x : G, x ^ 2 = 1) :
    IsElementaryAbelian 2 G := by
  have hinv (x : G) : x⁻¹ = x :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hsq x)
  refine
    { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
  calc
    a * b = (a * b)⁻¹ := (hinv _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
    _ = b * a := by rw [hinv, hinv]

private theorem square_one_mem_union
    {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hB : IsElementaryAbelian 2 B)
    (hAi : A.index = 2) (hBi : B.index = 2) (hne : A ≠ B)
    (hG : ¬ IsElementaryAbelian 2 G)
    (x : G) (hx : x ^ 2 = 1) : x ∈ A ∨ x ∈ B := by
  by_cases hxA : x ∈ A
  · exact Or.inl hxA
  by_cases hxB : x ∈ B
  · exact Or.inr hxB
  exfalso
  have hcard : Nat.card A = Nat.card B := by
    have hca := A.card_mul_index
    have hcb := B.card_mul_index
    rw [hAi] at hca
    rw [hBi] at hcb
    omega
  have hnot : ¬ A ≤ B := fun h => hne (eq_of_le_of_card_ge h hcard.symm.le)
  obtain ⟨a, haA, haB⟩ := SetLike.not_le_iff_exists.mp hnot
  have hxaB : x * a ∈ B := (B.mul_mem_iff_of_index_two hBi).mpr (by simp [hxB, haB])
  have hcentral (z : G) (hz : z ∈ A ⊓ B) : Commute z x := by
    have hza : Commute z a := congrArg Subtype.val
      (hA.toIsMulCommutative.is_comm.comm (⟨z, hz.1⟩ : A) ⟨a, haA⟩)
    have hzxa : Commute z (x * a) := congrArg Subtype.val
      (hB.toIsMulCommutative.is_comm.comm (⟨z, hz.2⟩ : B) ⟨x * a, hxaB⟩)
    simpa only [mul_inv_cancel_right] using hzxa.mul_right hza.inv_right
  apply hG
  apply elementary_of_all_square_one
  intro y
  by_cases hyA : y ∈ A
  · exact elemPow_eq_one_of_isElementaryAbelian y hyA
  by_cases hyB : y ∈ B
  · exact elemPow_eq_one_of_isElementaryAbelian y hyB
  have hyx : y * x ∈ A ⊓ B := ⟨
    (A.mul_mem_iff_of_index_two hAi).mpr (by simp [hyA, hxA]),
    (B.mul_mem_iff_of_index_two hBi).mpr (by simp [hyB, hxB])⟩
  have hyxsq : (y * x) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (y * x) hyx.1
  have hy : y = (y * x) * x := by
    rw [mul_assoc, ← pow_two, hx, mul_one]
  rw [hy, (hcentral (y * x) hyx).mul_pow, hyxsq, hx, one_mul]

/-- In a non-elementary finite group, two distinct elementary abelian
index-two subgroups contain every elementary abelian two-subgroup. -/
public theorem elementary_le_one_of_two_index_two
    {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hB : IsElementaryAbelian 2 B)
    (hAi : A.index = 2) (hBi : B.index = 2) (hne : A ≠ B)
    (hG : ¬ IsElementaryAbelian 2 G)
    (E : Subgroup G) (hE : IsElementaryAbelian 2 E) : E ≤ A ∨ E ≤ B := by
  apply SubgroupClass.subset_union.mp
  intro x hx
  exact square_one_mem_union A B hA hB hAi hBi hne hG x
    (elemPow_eq_one_of_isElementaryAbelian x hx)

end Subgroup
