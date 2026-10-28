module
public import Theory.GroupTheory.NoncentralChiefRefinement.BinarySections
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Mathlib.Order.Atoms.Finite
/-!
# A chief section moved by a commutator-generating subgroup

Let Q and K be normal subgroups, with Q a finite two-group and K
two-perfect. If [Q,K] is not contained in a specified normal layer Z,
choose a maximal proper normal subgroup of [Q,K]Z containing Z.
Coprime commutator idempotence makes K act nontrivially on the resulting
chief quotient. If K=[K,A], the same quotient must be moved by A.
Both endpoints are normal in the original acting group, and the quotient
lies between Z and Q. No irreducible-action witness is a hypothesis.

Source application: Aschbacher--Smith, original 15.2.27(2), printed p.1119,
constructing an actual partner chief section before displacement recognition.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

/-- Construct a chief interval above Z on which A acts nontrivially. -/
theorem exists_moved_chief_of_residual_commutator
    (Z Q K : NormalNode G) (A : Subgroup G)
    (hZQ : Z ≤ Q) (hQ : IsPGroup 2 Q.val) (hK : IsPPerfect 2 K.val)
    (hn : ¬ ⁅Q.val,K.val⁆ ≤ Z.val) (hgen : ⁅K.val,A⁆ = K.val) :
    ∃ B U : NormalNode G, Z ≤ B ∧ B ⋖ U ∧ U ≤ Q ∧
      ∃ a : A, sectionAction B U a ≠ 1 := by
  let C : NormalNode G := ⟨⁅Q.val,K.val⁆, inferInstanceAs (⁅Q.val,K.val⁆).Normal⟩
  have hCQ : C ≤ Q := commutator_le_left _ _
  let U : NormalNode G := C ⊔ Z
  have hZU : Z < U := lt_of_le_of_ne le_sup_right (by
    intro he
    apply hn
    change C ≤ Z
    exact (show C ≤ U from le_sup_left).trans he.ge)
  obtain ⟨B,hZB,hmax⟩ := Finite.exists_le_maximal
    (p := fun B : NormalNode G => B < U) (a := Z) hZU
  have hBU : B ⋖ U := ⟨hmax.prop, by
    intro W hBW hWU
    exact (not_le_of_gt hBW) (hmax.2 hWU hBW.le)⟩
  have hUQ : U ≤ Q := sup_le hCQ hZQ
  have hid : ⁅C.val,K.val⁆ = C.val :=
    commutator_isPPerfect_idempotent K.val Q.val hK hQ le_normalizer_of_normal
  have hnK : ¬ K.val ≤ (sectionAction B U).ker := by
    intro hk
    have hcomm : ⁅K.val,U.val⁆ ≤ B.val := by
      rw [commutator_le]
      intro k hkK u hu
      have he := DFunLike.congr_fun (hk hkK)
        (QuotientGroup.mk' (B.val.subgroupOf U.val) ⟨u,hu⟩)
      rw [sectionAction_mk] at he
      have hh := QuotientGroup.eq_iff_div_mem.mp he
      change k * u * k⁻¹ / u ∈ B.val at hh
      simpa only [div_eq_mul_inv, commutatorElement_def] using hh
    have hCB : C ≤ B := by
      change C.val ≤ B.val
      rw [← hid, commutator_comm]
      exact (commutator_mono le_rfl (show C.val ≤ U.val from le_sup_left)).trans hcomm
    exact hmax.prop.not_ge (sup_le hCB hZB)
  have hnA : ¬ A ≤ (sectionAction B U).ker := by
    intro ha
    apply hnK
    rw [← hgen]
    exact (commutator_mono le_rfl ha).trans (commutator_le_right _ _)
  obtain ⟨a,ha,hm⟩ := SetLike.not_le_iff_exists.mp hnA
  exact ⟨B,U,hZB,hBU,hUQ,⟨a,ha⟩,hm⟩
end NoncentralChiefRefinement
