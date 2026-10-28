module
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Cardinality of a union of transitive fibers

An invariant subset of a finite action is a union of any supplied transitive
fibers. Its cardinality is the sum of the corresponding fiber sizes. The
literal J.5 first-orbit consumer uses distance fibers of the native building.
-/

public noncomputable section
open scoped BigOperators
namespace MulAction
variable {K Ω I:Type*} [Group K] [MulAction K Ω] [Finite Ω] [Fintype I]

theorem invariant_set_fiber_sum (f:Ω→I)
    (htrans:∀x y,f x=f y→∃k:K,k•x=y) (S:Set Ω)
    (hS:∀k:K,∀x∈S,k•x∈S) (d:I→ℕ)
    (hd:∀i,Nat.card {x:Ω // f x=i}=d i) :
    ∃T:Finset I,(∀x,x∈S↔f x∈T) ∧ Nat.card S=∑i∈T,d i := by
  classical
  let T:=Finset.univ.filter (fun i=>∃x∈S,f x=i)
  have hmem (x:Ω) : x∈S↔f x∈T:=by
    constructor
    · intro hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hx,rfl⟩
    · intro hx
      obtain ⟨y,hy,he⟩:=(Finset.mem_filter.mp hx).2
      obtain ⟨k,hk⟩:=htrans y x he
      exact hk ▸ hS k y hy
  have hf (i:I) : Nat.card {x:S // f x.val=i}=if i∈T then d i else 0:=by
    by_cases hi:i∈T
    · let E:{x:S // f x.val=i}≃{x:Ω // f x=i}:=
        { toFun:=fun x=>⟨x.val.val,x.property⟩
          invFun:=fun x=>⟨⟨x.val,(hmem x).mpr (x.property.symm ▸ hi)⟩,x.property⟩
          left_inv:=fun _=>rfl
          right_inv:=fun _=>rfl }
      rw [if_pos hi,Nat.card_congr E,hd]
    · have : IsEmpty {x:S // f x.val=i}:=⟨fun x=>hi (x.property ▸ (hmem x.val).mp x.val.property)⟩
      simp [hi]
  refine ⟨T,hmem,?_⟩
  rw [←Nat.card_congr (Equiv.sigmaFiberEquiv (fun x:S=>f x.val)),Nat.card_sigma]
  simp only [hf]
  simp

end MulAction

