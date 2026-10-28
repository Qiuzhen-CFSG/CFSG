module
public import Theory.SpecificGroups.PSL2.BinaryFourFieldExtension
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.FieldDegree
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The marked field-involution centralizer in PSL₂(16):2

The field actor is the specified fourth-power Frobenius. Its fixed field has
four elements. Taking the fixed matrices and the order-two actor gives the
literal centralizer as PSL₂(4) × C₂, hence A₅ × C₂ through the existing
five-point projective action. The equivalence sends the specified involution
to the generator of the second factor.

This constructs H₃ in the model amalgam of Baumeister, *A geometry for groups
of J₃-type* (2007), printed p.498, preceding Corollary 2.10. The remaining
point, pair and intersection markings are separate obligations.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
open Theory.PSL2
open Theory.PSL2.BinaryFourFieldExtension
namespace Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam

abbrev Fixed := (fieldAut fieldInvolution).fixedSubgroup
abbrev Triangle := centralizer ({involution} : Set Model)

theorem fixedField_card :
    Nat.card (FixedBy.subfield (BinaryField 4) fieldInvolution) = 4 := by
  exact binary_fixedField_card (by decide) fieldInvolution
    (fun x => DFunLike.congr_fun fieldInvolution_square x) fieldInvolution_ne_one

def fixedEquiv : Fixed ≃* alternatingGroup (Fin 5) :=
  (fieldAutFixedEquiv fieldInvolution).trans
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four fixedField_card).some

theorem actor_fixes (a : Actor) (x : Fixed) : action a x = (x : BinaryGroup 4) := by
  obtain ⟨n, hn⟩ := a.property
  have hx : fieldAut fieldInvolution x = x := (MulAut.mem_fixedSubgroup _ _).mp x.property
  have ha : fieldAut a.val ∈ zpowers (fieldAut fieldInvolution) := by
    refine mem_zpowers_iff.mpr ⟨n, ?_⟩
    change fieldAutHom fieldInvolution ^ n = fieldAutHom a.val
    rw [← map_zpow]
    exact congrArg fieldAutHom hn
  exact smul_eq_self_of_mem_zpowers ha hx

theorem mem_triangle (x : Model) : x ∈ Triangle ↔ x.left ∈ Fixed := by
  rw [mem_centralizer_singleton_iff, MulAut.mem_fixedSubgroup]
  constructor
  · intro h
    have hh := congrArg SemidirectProduct.left h
    change x.left * action x.right 1 = 1 * fieldAut fieldInvolution x.left at hh
    simpa only [map_one, mul_one, one_mul] using hh.symm
  · intro h
    apply SemidirectProduct.ext
    · change x.left * action x.right 1 = 1 * fieldAut fieldInvolution x.left
      simpa only [map_one, one_mul, mul_one] using h.symm
    · change x.right * (⟨fieldInvolution, mem_zpowers _⟩ : Actor) =
        ⟨fieldInvolution, mem_zpowers _⟩ * x.right
      exact mul_comm _ _

def triangleProduct : Triangle ≃* Fixed × Actor where
  toFun x := (⟨x.val.left, (mem_triangle x.val).mp x.property⟩, x.val.right)
  invFun x := ⟨⟨x.1, x.2⟩, (mem_triangle _).mpr x.1.property⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_mul' x y := by
    apply Prod.ext
    · apply Subtype.ext
      change x.val.left * action x.val.right y.val.left = x.val.left * y.val.left
      rw [actor_fixes x.val.right ⟨y.val.left, (mem_triangle _).mp y.property⟩]
    · rfl

def actorGenerator : Actor := ⟨fieldInvolution, mem_zpowers _⟩

theorem actor_generated (a : Actor) : a ∈ zpowers actorGenerator := by
  obtain ⟨n, hn⟩ := a.property
  exact ⟨n, Subtype.ext hn⟩

def actorEquiv : Actor ≃* Multiplicative (ZMod 2) :=
  (zmodMulEquivOfGenerator actor_generated (by
    rw [Nat.card_zpowers, fieldInvolution_order])).symm

theorem actorEquiv_generator : actorEquiv actorGenerator = Multiplicative.ofAdd 1 :=
  zmodMulEquivOfGenerator_symm_apply_generator _ _

def triangleEquiv : Triangle ≃* (alternatingGroup (Fin 5) × Multiplicative (ZMod 2)) :=
  triangleProduct.trans (MulEquiv.prodCongr fixedEquiv actorEquiv)

theorem involution_mem_triangle : involution ∈ Triangle := by
  rw [mem_triangle]
  exact Fixed.one_mem

theorem triangleEquiv_involution :
    triangleEquiv ⟨involution, involution_mem_triangle⟩ = (1, Multiplicative.ofAdd 1) := by
  apply Prod.ext
  · exact fixedEquiv.map_one
  · exact actorEquiv_generator

theorem triangle_card : Nat.card Triangle = 120 := by
  rw [Nat.card_congr triangleEquiv.toEquiv, Nat.card_prod, nat_card_alternatingGroup]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Nat.factorial]

end Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam
