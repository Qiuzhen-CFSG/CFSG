module

public import Theory.SpecificGroups.BinaryFour.SplitBlockPair
public import Stellmacher.ElementaryAbelianMaxJMap
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Fintype.Pi

/-!
# The elementary Thompson subgroup of the binary unitriangular group

The six entries are (12,13,14,23,24,34). Multiplication and inversion are
those of upper unitriangular four-by-four matrices. The middle radical
has coordinates (13,14,23,24), exactly the published binary-four marking.

Every square-one element outside that radical has only twelve square-one
elements in its centralizer. Thus the radical is the unique largest
elementary abelian subgroup, and is the actual elementary Thompson
subgroup. The chosen root element 1+E23 also gives the literal subgroup
< a, [U,a] >, where U is the index-two subgroup with entry 23 zero.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007. This module proves the intrinsic Sylow calculation.
An identification with a split natural block, preserving its flag, is a
separate obligation; no such identification is assumed to follow from
these coordinate definitions.
-/

@[expose] public section
set_option synthInstance.maxSize 512

namespace Matrix.PSL3Two.SplitParabolic.Unitriangular
@[ext] structure T where
  x12 : ZMod 2
  x13 : ZMod 2
  x14 : ZMod 2
  x23 : ZMod 2
  x24 : ZMod 2
  x34 : ZMod 2
  deriving DecidableEq, Fintype
def oneT : T := ⟨0,0,0,0,0,0⟩
instance : One T := ⟨oneT⟩
def mulT (x y : T) : T := ⟨x.x12+y.x12, x.x13+y.x13+x.x12*y.x23,
 x.x14+y.x14+x.x12*y.x24+x.x13*y.x34, x.x23+y.x23,x.x24+y.x24+x.x23*y.x34,x.x34+y.x34⟩
instance : Mul T := ⟨mulT⟩
def invT (x : T) : T := ⟨x.x12,x.x13+x.x12*x.x23,
 x.x14+x.x12*x.x24+x.x13*x.x34+x.x12*x.x23*x.x34,x.x23,x.x24+x.x23*x.x34,x.x34⟩
instance : Inv T := ⟨invT⟩
instance : Group T where
 mul_assoc x y z := by
  change mulT (mulT x y) z = mulT x (mulT y z)
  ext <;> simp only [mulT] <;> ring
 one_mul x := by
  change mulT oneT x = x
  ext <;> simp [mulT, oneT]
 mul_one x := by
  change mulT x oneT = x
  ext <;> simp [mulT, oneT]
 inv_mul_cancel x := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  change mulT (invT x) x = oneT
  ext <;> simp only [mulT, invT, oneT] <;> ring_nf <;> simp [h2]
end Matrix.PSL3Two.SplitParabolic.Unitriangular

namespace Matrix.PSL3Two.SplitParabolic.Unitriangular
open Subgroup BinaryFourSplitPair

def sixteen (v : E) : T := ⟨0,v.toAdd 0,v.toAdd 1,v.toAdd 2,v.toAdd 3,0⟩
def middle : E →* T where
 toFun := sixteen
 map_one' := rfl
 map_mul' v w := by
  change sixteen (v*w) = mulT (sixteen v) (sixteen w)
  ext <;> simp [sixteen,mulT]

def A : Subgroup T where
 carrier := {x | x.x12=0 ∧ x.x34=0}
 one_mem' := ⟨rfl,rfl⟩
 mul_mem' := by rintro x y ⟨hx,hx'⟩ ⟨hy,hy'⟩; exact ⟨by change x.x12+y.x12=0; rw [hx,hy]; rfl,by change x.x34+y.x34=0; rw [hx',hy']; rfl⟩
 inv_mem' := fun hx => hx
instance : DecidablePred (· ∈ A) := fun x => inferInstanceAs (Decidable (x.x12=0 ∧ x.x34=0))

def coordinates : A ≃* E where
 toFun x := Multiplicative.ofAdd ![x.val.x13,x.val.x14,x.val.x23,x.val.x24]
 invFun v := ⟨sixteen v, rfl, rfl⟩
 left_inv x := by apply Subtype.ext; ext <;> simp [sixteen, x.property.1, x.property.2]
 right_inv v := by funext i; fin_cases i <;> rfl
 map_mul' x y := by
  change (fun i => ![(mulT x.val y.val).x13,(mulT x.val y.val).x14,(mulT x.val y.val).x23,(mulT x.val y.val).x24] i) =
    (fun i => ![x.val.x13,x.val.x14,x.val.x23,x.val.x24] i + ![y.val.x13,y.val.x14,y.val.x23,y.val.x24] i)
  funext i; fin_cases i <;> simp [mulT, x.property.1, y.property.2]

theorem card_A : Nat.card A = 16 := (Nat.card_congr coordinates.toEquiv).trans BinaryFourSplitPair.card_E
instance : IsElementaryAbelian 2 A where
 is_comm.comm x y := coordinates.injective (by simp only [map_mul]; exact mul_comm _ _)
 exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
  coordinates.injective (by rw [map_pow,map_one]; exact (by decide +kernel : ∀ v : E, v^2=1) _))

def Square (x : T) : Prop := x.x12*x.x23=0 ∧ x.x12*x.x24+x.x13*x.x34=0 ∧ x.x23*x.x34=0
def Commutes (x y : T) : Prop := x.x12*y.x23=y.x12*x.x23 ∧
 x.x12*y.x24+x.x13*y.x34=y.x12*x.x24+y.x13*x.x34 ∧ x.x23*y.x34=y.x23*x.x34
instance (x : T) : Decidable (Square x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
instance (x y : T) : Decidable (Commutes x y) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
theorem square_iff (x : T) : x^2=1 ↔ Square x := by
 have h2 (u : ZMod 2) : u+u=0 := by exact (by decide : ∀ u : ZMod 2, u+u=0) u
 rw [pow_two]
 change mulT x x = oneT ↔ _
 simp only [T.ext_iff, mulT, oneT, Square, h2, zero_add, true_and, and_true]
theorem commute_iff (x y : T) : x*y=y*x ↔ Commutes x y := by
 have h (u v s t : ZMod 2) : u+v+s=v+u+t ↔ s=t := by
  rw [add_comm v u, add_right_inj]
 change mulT x y = mulT y x ↔ _
 simp only [T.ext_iff, mulT, Commutes, add_assoc (x.x14+y.x14), add_assoc (y.x14+x.x14), h,
  add_comm y.x12 x.x12, add_comm y.x23 x.x23, add_comm y.x34 x.x34, true_and, and_true]

theorem census : ∀ x : T, Square x → x ∉ A →
 Fintype.card {y : T // Square y ∧ Commutes x y} < 16 := by decide +kernel
end Matrix.PSL3Two.SplitParabolic.Unitriangular

namespace Matrix.PSL3Two.SplitParabolic.Unitriangular
open Subgroup
open scoped IsMulCommutative

theorem large_elementary_le (B : Subgroup T) [IsElementaryAbelian 2 B]
    (hcard : 16 ≤ Nat.card B) : B ≤ A := by
 intro x hx
 by_contra hn
 have hs : Square x := (square_iff x).mp (elemPow_eq_one_of_isElementaryAbelian x hx)
 let f : B → {y : T // Square y ∧ Commutes x y} := fun y =>
  ⟨y, (square_iff y).mp (elemPow_eq_one_of_isElementaryAbelian (y : T) y.property),
    (commute_iff x y).mp (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : B) y))⟩
 have hi : Function.Injective f := fun y z h => Subtype.ext (congrArg (fun v : {y : T // Square y ∧ Commutes x y} => v.val) h)
 have hc := Nat.card_le_card_of_injective f hi
 have hlt : Nat.card {y : T // Square y ∧ Commutes x y} < 16 := by
  simpa only [Nat.card_eq_fintype_card] using census x hs hn
 omega

theorem max_elementary_family : Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T) = {A} := by
 ext B
 constructor
 · intro hB
   let _ : IsElementaryAbelian 2 B := hB.2.1
   have hc : 16 ≤ Nat.card B := by simpa only [card_A] using hB.2.2 A le_top inferInstance
   exact Subgroup.eq_of_le_of_card_ge (large_elementary_le B hc) (by simpa only [card_A] using hc)
 · rintro rfl
   refine ⟨le_top, inferInstance, ?_⟩
   intro B _ hB
   let _ : IsElementaryAbelian 2 B := hB
   by_cases hc : 16 ≤ Nat.card B
   · exact Subgroup.card_le_of_le (large_elementary_le B hc)
   · rw [card_A]; omega

theorem thompson_eq : Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup T) = A := by
 rw [Stellmacher.elementaryAbelianMaxJ, max_elementary_family, sSup_singleton]
end Matrix.PSL3Two.SplitParabolic.Unitriangular

namespace Matrix.PSL3Two.SplitParabolic.Unitriangular
open Subgroup BinaryFourSplitPair
open scoped commutatorElement

def U : Subgroup T where
 carrier := {x | x.x23=0}
 one_mem' := rfl
 mul_mem' := by intro x y hx hy; change x.x23+y.x23=0; rw [hx,hy]; rfl
 inv_mem' := fun hx => hx
instance : DecidablePred (· ∈ U) := fun x => inferInstanceAs (Decidable (x.x23=0))

def W : Subgroup T where
 carrier := {x | x.x24=0 ∧ x.x34=0}
 one_mem' := ⟨rfl,rfl⟩
 mul_mem' := by
  rintro x y ⟨hx,hx'⟩ ⟨hy,hy'⟩
  change x.x24+y.x24+x.x23*y.x34=0 ∧ x.x34+y.x34=0
  simp only [hx,hx',hy,hy',mul_zero,add_zero]
  trivial
 inv_mem' := by
  intro x hx
  change x.x24+x.x23*x.x34=0 ∧ x.x34=0
  simp only [hx.1,hx.2,mul_zero,add_zero]
  trivial
instance : DecidablePred (· ∈ W) := fun x => inferInstanceAs (Decidable (x.x24=0 ∧ x.x34=0))

def z : T := ⟨0,0,1,0,0,0⟩
def a : T := ⟨0,0,0,1,0,0⟩
def r : T := ⟨1,0,0,0,0,0⟩
def q : T := ⟨0,0,0,0,0,1⟩
def bit (i : Fin 4) : T := sixteen (Multiplicative.ofAdd (Pi.single i 1))

theorem a_selected : a ∈ W ∧ a ∉ U ∧ a^2=1 := by decide +kernel
theorem z_mem_A : z ∈ A := by decide
theorem coordinates_z : coordinates ⟨z,z_mem_A⟩ = point := rfl
theorem z_central : z ∈ center T := by
 rw [mem_center_iff]
 decide +kernel
theorem z_ne_one : z ≠ 1 := by decide

theorem row_action : ∀ v : E, r * middle v * r⁻¹ = middle (BinaryFourSplitPair.row v) := by decide +kernel
theorem column_action : ∀ v : E, q * middle v * q⁻¹ = middle (column v) := by decide +kernel

theorem middle_eq_bits : ∀ v : E,
 middle v = bit 0 ^ (v.toAdd 0).val * bit 1 ^ (v.toAdd 1).val *
  bit 2 ^ (v.toAdd 2).val * bit 3 ^ (v.toAdd 3).val := by decide +kernel

theorem A_eq_closure_bits : A = closure (Set.range bit) := by
 apply le_antisymm
 · intro x hx
   let v := coordinates ⟨x,hx⟩
   have he : middle v=x := by exact congrArg Subtype.val (coordinates.symm_apply_apply ⟨x,hx⟩)
   rw [← he,middle_eq_bits]
   have hbit (i : Fin 4) : bit i ∈ closure (Set.range bit) := subset_closure ⟨i,rfl⟩
   exact mul_mem (mul_mem (mul_mem
    (pow_mem (hbit 0) _) (pow_mem (hbit 1) _))
    (pow_mem (hbit 2) _)) (pow_mem (hbit 3) _)
 · apply (closure_le _).mpr
   rintro x ⟨i,rfl⟩
   trivial

instance : A.Normal where
 conj_mem x hx g := by
  change (mulT (mulT g x) (invT g)).x12=0 ∧ (mulT (mulT g x) (invT g)).x34=0
  have h2 : ∀ t : ZMod 2, t+t=0 := by decide
  simp only [mulT,invT,hx.1,hx.2,add_zero,h2]
  trivial

theorem a_generates : zpowers a ⊔ ⁅U,zpowers a⁆ = A := by
 apply le_antisymm
 · apply sup_le
   · exact zpowers_le.mpr ⟨rfl,rfl⟩
   · exact (commutator_mono (le_refl U) (zpowers_le.mpr (show a ∈ A from ⟨rfl,rfl⟩))).trans
      (commutator_le_right U A)
 · rw [A_eq_closure_bits]
   apply (closure_le _).mpr
   have hr : r ∈ U := rfl
   have hq : q ∈ U := rfl
   have ha : a ∈ zpowers a := mem_zpowers a
   have hb : bit 0 ∈ ⁅U,zpowers a⁆ := by
    have he : ⁅r,a⁆=bit 0 := by decide +kernel
    exact he ▸ commutator_mem_commutator hr ha
   have he : bit 3 ∈ ⁅U,zpowers a⁆ := by
    have he : ⁅q,a⁆=bit 3 := by decide +kernel
    exact he ▸ commutator_mem_commutator hq ha
   have hz : bit 1 ∈ ⁅U,zpowers a⁆ := by
    have hi : ⁅r*q,a⁆ * bit 0 * bit 3 = bit 1 := by decide +kernel
    rw [← hi]
    exact mul_mem (mul_mem (commutator_mem_commutator (U.mul_mem hr hq) ha) hb) he
   rintro x ⟨i,rfl⟩
   fin_cases i
   · exact (show ⁅U,zpowers a⁆ ≤ zpowers a ⊔ ⁅U,zpowers a⁆ from le_sup_right) hb
   · exact (show ⁅U,zpowers a⁆ ≤ zpowers a ⊔ ⁅U,zpowers a⁆ from le_sup_right) hz
   · exact (show zpowers a ≤ zpowers a ⊔ ⁅U,zpowers a⁆ from le_sup_left) ha
   · exact (show ⁅U,zpowers a⁆ ≤ zpowers a ⊔ ⁅U,zpowers a⁆ from le_sup_right) he
end Matrix.PSL3Two.SplitParabolic.Unitriangular

namespace Matrix.PSL3Two.SplitParabolic.Unitriangular
open Subgroup

/-- The whole unitriangular Sylow model has order sixty-four. -/
public theorem card_T : Nat.card T = 64 := by rw [Nat.card_eq_fintype_card]; decide +kernel
public theorem card_U : Nat.card U = 32 := by rw [Nat.card_eq_fintype_card]; decide +kernel
public theorem card_W : Nat.card W = 16 := by rw [Nat.card_eq_fintype_card]; decide +kernel

/-- Outside membership alone does not select an involution, even in this
split model. This does not refute the full ambient source theorem. -/
public theorem outside_order_four : r*a ∈ W ∧ r*a ∉ U ∧ (r*a)^2 ≠ 1 ∧ (r*a)^4=1 := by
 decide +kernel

/-- Every outside involution of the displayed W belongs to the middle sixteen. -/
public theorem outside_involution_mem_A : ∀ x : T, x ∈ W → x ∉ U → x^2=1 → x ∈ A := by
 decide +kernel

end Matrix.PSL3Two.SplitParabolic.Unitriangular

namespace Matrix.PSL3Two.SplitParabolic.Unitriangular
/-- Two root coordinates complement the middle radical in the entire Sylow group. -/
public theorem normal_form (x : T) :
 x = middle (Multiplicative.ofAdd
   ![x.x13, x.x14+x.x13*x.x34, x.x23, x.x24+x.x23*x.x34]) *
   r ^ x.x12.val * q ^ x.x34.val := by
 revert x
 decide +kernel
end Matrix.PSL3Two.SplitParabolic.Unitriangular
