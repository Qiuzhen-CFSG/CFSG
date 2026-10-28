module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

/-!
# Fusion of an involution coset over an elementary abelian subgroup

If an involution j normalizes an elementary abelian two-group A and
C_A(j) is contained in [A,j], every square-one element of Aj is conjugate
to j by A. The commutator map a ↦ [a,j] is a homomorphism onto [A,j].
The involution equation places the displacement in its fixed subgroup,
and the fixed-point hypothesis supplies the required conjugator.

This is the group-theoretic consequence of the binary-module calculation
used in Aschbacher–Smith I.2.2(5), printed p.412 / PDF p.423. The module
calculation C_A(j)=[A,j] remains an explicit hypothesis.
-/

public section
open Subgroup
open scoped commutatorElement

namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem elementary_involution_coset_fusion (A : Subgroup G) [A.Normal]
    [IsElementaryAbelian 2 A] (j : G) (hj : orderOf j = 2)
    (hfixed : A ⊓ centralizer ({j} : Set G) ≤ ⁅A, zpowers j⁆)
    (x : G) (hx : x ^ 2 = 1) (hcoset : x * j⁻¹ ∈ A) :
    ∃ a : A, (a : G) * j * (a : G)⁻¹ = x := by
  have hnormal : zpowers j ≤ normalizer (A : Set G) := by
    rw [A.normalizer_eq_top]
    exact le_top
  have hcommA : ⁅A, zpowers j⁆ ≤ A :=
    le_normalizer_iff_commutator_le_left.mp hnormal
  have hcentral : A ≤ centralizer (A : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  let f : A →* G := {
    toFun := fun a => ⁅(a : G), j⁆
    map_one' := by simp
    map_mul' := by
      intro a b
      change ⁅(a : G) * (b : G), j⁆ = ⁅(a : G), j⁆ * ⁅(b : G), j⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have ha : ⁅(a : G), j⁆ ∈ A :=
        hcommA (commutator_mem_commutator a.property (mem_zpowers j))
      have hb : ⁅(b : G), j⁆ ∈ A :=
        hcommA (commutator_mem_commutator b.property (mem_zpowers j))
      rw [← hcentral a.property _ hb, mul_inv_cancel_right, hcentral ha _ hb] }
  have hrange : f.range = ⁅A, zpowers j⁆ := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      exact commutator_mem_commutator a.property (mem_zpowers j)
    · apply commutator_le.mpr
      intro a ha b hb
      have hb' : b = 1 ∨ b = j := by
        have hc : Nat.card (zpowers j) = 2 := by rw [Nat.card_zpowers, hj]
        obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : zpowers j)).mp hc
        by_cases h : b = 1
        · exact Or.inl h
        · right
          have hj1 : j ≠ 1 := by intro h; simp [h] at hj
          exact congrArg Subtype.val
            ((hz ⟨b, hb⟩ (by simpa using h)).trans
              (hz ⟨j, mem_zpowers j⟩ (by simpa using hj1)).symm)
      rcases hb' with rfl | rfl
      · simp
      · exact ⟨⟨a, ha⟩, rfl⟩
  have hj2 : j ^ 2 = 1 := hj ▸ pow_orderOf_eq_one j
  let y := x * j⁻¹
  have hy2 : y ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian y hcoset
  have hcocycle : y * (j * y * j⁻¹) = 1 := by
    calc
      _ = x ^ 2 * (j ^ 2)⁻¹ := by dsimp [y]; simp only [pow_two]; group
      _ = 1 := by rw [hx, hj2]; simp
  have hfix : j * y * j⁻¹ = y :=
    (mul_left_cancel (hcocycle.trans (by simpa only [pow_two] using hy2.symm)))
  have hycomm : y ∈ centralizer ({j} : Set G) :=
    mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hym : y ∈ f.range := hrange ▸ hfixed ⟨hcoset, hycomm⟩
  obtain ⟨a, ha⟩ := hym
  refine ⟨a, ?_⟩
  change (a : G) * j * (a : G)⁻¹ * j⁻¹ = x * j⁻¹ at ha
  exact mul_right_cancel ha

end Theory.GroupTheory
