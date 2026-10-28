module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Coordinates
public import Theory.Mathieu.M24.Properties.InvolutionClasses

/-!
# A native six-fixed-point cubic representative

We use the existing native second generator, whose order and support have
been checked in the kernel. Passing to its generated subgroup retains the
literal common fixed-point set. This is the six-fixed-point structural
convention needed in Aschbacher–Smith H.15.7 (printed pp.401–402).
The shared historical names `m24Element3A` and `m24Element3B` are preserved;
no class identification follows merely from those names. Conjugacy to this
representative is proved in the companion `Conjugacy` module.
-/

@[expose] public section

open Sporadic.Mathieu
namespace MathieuCode.SixPoint
noncomputable section
open scoped Pointwise

/-- The native six-fixed-point cubic, independently of the historical class labels. -/
def cubicRepresentative : M24 := ⟨m24Element3B, m24Element3B_mem⟩
def cubicSubgroup : Subgroup M24 := Subgroup.zpowers cubicRepresentative

theorem cubicRepresentative_order : orderOf cubicRepresentative = 3 := by
  rw [← Subgroup.orderOf_coe]
  exact m24Element3B_order

theorem cubicSubgroup_card : Nat.card cubicSubgroup = 3 := by
  rw [cubicSubgroup, Nat.card_zpowers, cubicRepresentative_order]

theorem mem_fixedPoint_zpowers_iff (g : M24) (i : Fin 24) :
    i ∈ MulAction.fixedPoints (Subgroup.zpowers g) (Fin 24) ↔ g • i = i := by
  constructor
  · intro h
    exact h ⟨g, Subgroup.mem_zpowers g⟩
  · intro h d
    obtain ⟨k, hk⟩ := d.property
    change d.val • i = i
    rw [← hk]
    exact MulAction.mem_fixedBy_zpow h k

theorem cubicSubgroup_fixed_card : Nat.card (FixedPoint cubicSubgroup) = 6 := by
  classical
  let e : FixedPoint cubicSubgroup ≃ {i : Fin 24 // i ∈ m24Element3B.supportᶜ} :=
    Equiv.subtypeEquivRight fun i => by
      rw [cubicSubgroup, mem_fixedPoint_zpowers_iff]
      simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_compl, Fintype.card_fin, m24Element3B_fixed_card]

end
end MathieuCode.SixPoint
