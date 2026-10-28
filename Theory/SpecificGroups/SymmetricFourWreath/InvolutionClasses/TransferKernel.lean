module
public import Theory.SpecificGroups.SymmetricFourWreath.InvolutionClasses.Classes
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.Group.Int.Units

/-!
# The index-two transfer subgroup of the symmetric wreath group

Multiply the two factor signs and the swapping sign. The kernel has
index two in the marked Sylow, and its involutions are precisely source
classes Δ1, Δ2 and Δ4. This gives the actual subgroup used in Thompson
transfer in Aschbacher–Smith 13.9.9, printed p.972.
-/

@[expose] public section
namespace SymmetricFourWreath.InvolutionClasses
open Subgroup

def turnSign : C2 →* ℤˣ where
  toFun q := if q=1 then 1 else -1
  map_one' := by simp
  map_mul' := by decide +kernel

def baseSign : W →* ℤˣ where
  toFun x := Equiv.Perm.sign (x.left 1)*Equiv.Perm.sign (x.left turn)
  map_one' := by simp
  map_mul' x y := by
    rcases c2_eq_one_or_turn x.right with hx|hx
    · simp [hx,mul_comm,mul_left_comm]
    · simp [hx,mul_comm,mul_left_comm]

def transferSign : W →* ℤˣ := baseSign * (turnSign.comp RegularWreathProduct.rightHom)

def transferKernel : Subgroup W := transferSign.ker

theorem transferSign_swap : transferSign swap=-1 := by decide +kernel

theorem transferSign_representative : ∀i:Fin 6,
    transferSign (representative i)=1 ↔ i=0 ∨ i=1 ∨ i=3 := by decide +kernel

theorem transferKernel_involution (x : W) (ho : orderOf x=2) :
    x∈transferKernel ↔ classIndex x=0 ∨ classIndex x=1 ∨ classIndex x=3 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (involution_representative x (by simpa only [ho,pow_two] using pow_orderOf_eq_one x)
      (by intro h;simp [h] at ho))
  change transferSign x=1 ↔ _
  have hs : transferSign x=transferSign (representative (classIndex x)) := by
    calc
      _ = transferSign (g*representative (classIndex x)*g⁻¹) := congrArg transferSign hg.symm
      _ = _ := by rw [map_mul,map_mul,map_inv]; exact mul_inv_cancel_comm _ _
  rw [hs,transferSign_representative]

theorem transferKernel_sylow_index :
    (transferKernel.subgroupOf (standardSylow:Subgroup W)).index=2 := by
  let f : (standardSylow:Subgroup W)→*ℤˣ := transferSign.comp (standardSylow:Subgroup W).subtype
  have hf : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl|rfl
    · exact ⟨1,map_one f⟩
    · exact ⟨⟨swap,swap_mem_standardSylow⟩,transferSign_swap⟩
  have hk : f.ker=transferKernel.subgroupOf (standardSylow:Subgroup W) := rfl
  rw [←hk,index_ker,MonoidHom.range_eq_top.mpr hf,Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup ℤˣ) ≃* ℤˣ).toEquiv]
  rw [Nat.card_eq_fintype_card]
  decide +kernel

end SymmetricFourWreath.InvolutionClasses
