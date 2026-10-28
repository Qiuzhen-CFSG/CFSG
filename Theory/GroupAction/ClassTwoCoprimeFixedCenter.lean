module

public import Theory.GroupAction.CoprimeSmallQuotient
public import Theory.GroupAction.CoprimeHall

/-!
# The center of the fixed group in a coprime class-two action

Fixing the original center pointwise makes the full fixed subgroup normal.
The action commutator centralizes it, and coprime decomposition generates the
whole original group. Thus an element central in the fixed subgroup is
already central in the original group.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupAction

/-- The full fixed subgroup retains exactly the original central elements. -/
theorem center_fixed_eq_of_class_two_coprime
    {P A : Type*} [Group P] [Group A] [Finite P] [Finite A]
    [MulDistribMulAction A P]
    (hs : Group.IsSolvable P) (hcop : Nat.Coprime (Nat.card A) (Nat.card P))
    (hclass : _root_.commutator P ≤ center P)
    (hfix : ∀ a : A, ∀ z : center P, a • (z : P) = z) :
    center (fixedPointSubgroup A P) = (center P).subgroupOf (fixedPointSubgroup A P) := by
  let F := fixedPointSubgroup A P
  let C := commutatorAction A P
  have hFn : F.Normal := by
    constructor
    intro x hx y a
    have hc : ⁅y,x⁆ ∈ center P := hclass
      (commutator_mem_commutator (mem_top y) (mem_top x))
    have he : y*x*y⁻¹ = ⁅y,x⁆*x := by simp [commutatorElement_def,mul_assoc]
    rw [he,smul_mul',hfix a ⟨_,hc⟩,hx a]
  let _ := hFn
  have hCF : C ≤ centralizer (F : Set P) :=
    commutatorAction_le_centralizer_of_fixed_normal F (fun a _ hx => hx a)
  have hgen : F ⊔ C = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime hs hcop
  ext x
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro y
    obtain ⟨f,hf,c,hc,rfl⟩ := mem_sup_of_normal_left.mp (hgen ▸ mem_top y)
    have hfcomm : Commute f (x:P) :=
      congrArg Subtype.val (mem_center_iff.mp hx (⟨f,hf⟩ : F))
    have hccomm : Commute c (x:P) := (hCF hc x x.property).symm
    exact (hfcomm.mul_left hccomm).eq
  · intro hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp hx y)

end Theory.GroupAction
