module
public import Theory.GroupTheory.WeakBNPair.RegularTree.SevenCartanPaths

/-!
# An order-seven subgroup fixes the full cubic star

The fixed-point congruence and the bound of three neighbors force every
neighbor to be fixed. The conclusion is the full permutation kernel, with
no replacement by a vertex two-core.
-/

public noncomputable section
open Subgroup SimpleGraph
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace Theory.GroupTheory.WeakBNPair.RegularTree
variable {X : Type*} [Group X] (F : Bool → Subgroup X)

/-- A subgroup of order seven fixing a cubic vertex lies in its whole
radius-one permutation kernel. -/
theorem seven_cubic_vertex_kernel (C : Subgroup X) (hC : Nat.card C=7)
    (v : Vertex F) (hCv : C ≤ stabilizer F v)
    (hval : Nat.card ((graph F).neighborSet v)=3) : C ≤ ballKernel F v 1 := by
  let a := (localAction F v).comp (inclusion hCv)
  let : MulAction C ((graph F).neighborSet v) := MulAction.compHom _ a
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Finite C := Nat.finite_of_card_ne_zero (by rw [hC]; decide)
  let : Finite ((graph F).neighborSet v) := Nat.finite_of_card_ne_zero (by rw [hval]; decide)
  have hp : IsPGroup 7 C := IsPGroup.of_card (n := 1) (by simpa using hC)
  have hm := hp.card_modEq_card_fixedPoints ((graph F).neighborSet v)
  let B := MulAction.fixedPoints C ((graph F).neighborSet v)
  have hinj : Function.Injective (Subtype.val : B → (graph F).neighborSet v) := Subtype.val_injective
  have hle := Nat.card_le_card_of_injective _ hinj
  have he : Nat.card ((graph F).neighborSet v) ≤ Nat.card B := by
    change Nat.card ((graph F).neighborSet v) % 7 = Nat.card B % 7 at hm
    rw [hval] at hm hle ⊢
    omega
  have hs := hinj.bijective_of_nat_card_le he
  intro x hx w hw
  rcases (mem_ball_one F v w).mp hw with hw | rfl
  · obtain ⟨z,hz⟩ := hs.2 (⟨w,hw⟩ : (graph F).neighborSet v)
    have he : z.val.val=w := congrArg Subtype.val hz
    rw [←he]
    exact congrArg Subtype.val (z.property (⟨x,hx⟩ : C))
  · exact hCv hx

end Theory.GroupTheory.WeakBNPair.RegularTree
