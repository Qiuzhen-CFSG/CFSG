module

public import Theory.GroupTheory.InvolutionTransfer
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Covering ambient involution classes by transfer

Every ambient involution has a conjugate in an index-two subgroup of a
Sylow two-subgroup when the ambient group has no normal subgroup of index
two. Thus any family of ambient classes covering the involutions of that
smaller subgroup covers all ambient involutions. Nonabelian simplicity
discharges the normal-index hypothesis.

Source: Thompson transfer, Aschbacher–Smith A.1.36, applied in the proof
of 13.9.9(5), printed p.972 (PDF p.989).
-/

public section

namespace Sylow

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Transfer into an index-two Sylow subgroup, for an involution not
necessarily already in the chosen Sylow subgroup. -/
theorem exists_isConj_mem_of_index_two_ambient
    (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (U : Subgroup S) (hU : U.index = 2) (x : G) (hx : orderOf x = 2) :
    ∃ y : S, y ∈ U ∧ IsConj x (y : G) := by
  have hp : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  have hxS : MulAut.conj g x ∈ (S : Subgroup G) := by
    rw [← hg]
    exact mem_map_of_mem _ (hP (mem_zpowers x))
  let xS : S := ⟨MulAut.conj g x, hxS⟩
  have hconj : IsConj x (xS : G) := isConj_iff.mpr ⟨g, rfl⟩
  have hxSorder : orderOf xS = 2 := by
    rw [← Subgroup.orderOf_coe xS]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  obtain ⟨y, hxy, hy⟩ := S.exists_isConj_mem_of_index_two hno U hU xS hxSorder
  exact ⟨y, hy, hconj.trans hxy⟩

/-- Covering the involutions in an index-two Sylow subgroup by ambient
classes is enough to cover every ambient involution. -/
theorem involution_classes_covered_of_index_two
    (S : Sylow 2 G)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (U : Subgroup S) (hU : U.index = 2) (representatives : Set G)
    (hcover : ∀ y : S, y ∈ U → orderOf (y : G) = 2 →
      ∃ r ∈ representatives, IsConj r (y : G)) :
    ∀ x : G, orderOf x = 2 → ∃ r ∈ representatives, IsConj r x := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := S.exists_isConj_mem_of_index_two_ambient hno U hU x hx
  have hyorder : orderOf (y : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  obtain ⟨r, hr, hry⟩ := hcover y hy hyorder
  exact ⟨r, hr, hry.trans hxy.symm⟩

end Sylow

namespace Subgroup

variable {G : Type*} [Group G] [IsSimpleGroup G]

/-- Nonabelian simplicity supplies the absence of normal index two needed
by Thompson transfer. -/
theorem index_ne_two_of_nonabelian_simple (hG : ¬ IsMulCommutative G)
    (N : Subgroup G) (hN : N.Normal) : N.index ≠ 2 := by
  rcases hN.eq_bot_or_eq_top with rfl | rfl
  · rw [index_bot]
    intro hcard
    let : IsCyclic G := isCyclic_of_prime_card hcard
    exact hG inferInstance
  · simp

end Subgroup
