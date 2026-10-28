module
public import BenderSuzuki.External.Huppert.II.theorem_8_27
/-!
# Sylow subgroups under an embedding into binary PSL₂

A two-subgroup of PSL₂ over a finite field of characteristic two lies in an
actual Sylow subgroup, which is isomorphic to the additive field. Injectivity
therefore makes every Sylow two-subgroup of the original group commutative.
Source: Huppert II.8.2(a); used in Aschbacher–Smith 2.5.19, p.561.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2

/-- A genuine binary PSL₂ embedding makes every original Sylow two-subgroup commutative. -/
theorem binary_sylow_commutative_of_injective {F K:Type*}
    [Field F] [Finite F] [CharP F 2] [_root_.Group K] [Finite K]
    (f:K→*PSL(2,F)) (hf:Function.Injective f) (P:Sylow 2 K) :
    IsMulCommutative P := by
  let := Fintype.ofFinite F
  obtain ⟨n,_,hn⟩:=FiniteField.card F 2
  obtain ⟨Q,hQ⟩:=(P.isPGroup'.map f).exists_le_sylow
  obtain ⟨e⟩:=BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
    (show Nat.card F=2^(n:ℕ) by simpa only [Nat.card_eq_fintype_card] using hn) Q
  let j:P→*Q:=(f.comp (P:Subgroup K).subtype).codRestrict Q
    (fun x=>hQ ⟨x,x.property,rfl⟩)
  have hj:Function.Injective j:=by
    intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  refine ⟨⟨fun x y=>?_⟩⟩
  apply hj
  rw [map_mul,map_mul]
  apply e.symm.injective
  simp only [map_mul]
  exact mul_comm _ _
end Theory.PSL2

