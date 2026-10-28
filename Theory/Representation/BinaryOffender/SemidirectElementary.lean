module
public import Theory.Representation.BinaryOffender.EndFieldTransfer
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.FieldTheory.Finiteness

/-!
# Elementary subgroups in binary semidirect products

For a commutative subgroup of a binary affine group, its projection kernel
injects into the fixed space of its projected actor. Counting the kernel and
image therefore bounds the subgroup order by the actor order times the fixed
space order. If an elementary subgroup is at least as large as the translation
module and has nontrivial projection, that projection is an offender.

Application: Aschbacher–Smith 14.3.20, where B.3.2 excludes offenders in the
alternating action on the deleted six-letter module.
-/

@[expose] public section
namespace Representation.BinaryOffender
open Subgroup SemidirectProduct
open scoped IsMulCommutative
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
theorem semidirect_commutative_card_le
    (ρ : Representation (ZMod 2) G V) (φ : G →* MulAut (Multiplicative V))
    (hφ : ∀ g v, (φ g (Multiplicative.ofAdd v)).toAdd=ρ g v)
    (E : Subgroup (Multiplicative V ⋊[φ] G)) [IsMulCommutative E] :
    Nat.card E ≤ Nat.card (E.map rightHom) * Nat.card (fixedSpace ρ (E.map rightHom)) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let f : E →* G := rightHom.comp E.subtype
  have hr : f.range=E.map rightHom := by
    ext g
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  let j : f.ker → fixedSpace ρ (E.map rightHom) := fun x =>
    ⟨x.val.val.left.toAdd,by
      intro a
      obtain ⟨y,hy,ha⟩ := a.property
      have hx : x.val.val.right=1 := x.property
      have hc := congrArg (fun z : E => z.val.left)
        (mul_comm (⟨y,hy⟩ : E) x.val)
      change y.left * φ y.right x.val.val.left =
        x.val.val.left * φ x.val.val.right y.left at hc
      rw [hx,map_one,MulAut.one_apply,mul_comm x.val.val.left y.left] at hc
      have he := mul_left_cancel hc
      change ρ a.val x.val.val.left.toAdd=x.val.val.left.toAdd
      rw [←ha,←hφ]
      exact congrArg Multiplicative.toAdd he⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply SemidirectProduct.ext
    · exact Multiplicative.toAdd.injective (congrArg Subtype.val h)
    · exact x.property.trans y.property.symm
  have hc : Nat.card f.ker * Nat.card (E.map rightHom)=Nat.card E := by
    rw [←hr,←Subgroup.index_ker]
    exact f.ker.card_mul_index
  calc
    Nat.card E=Nat.card f.ker * Nat.card (E.map rightHom) := hc.symm
    _≤Nat.card (fixedSpace ρ (E.map rightHom))*Nat.card (E.map rightHom) :=
      Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective j hj)
    _=Nat.card (E.map rightHom)*Nat.card (fixedSpace ρ (E.map rightHom)) := Nat.mul_comm _ _

theorem semidirect_elementary_image_offender
    (ρ : Representation (ZMod 2) G V) (φ : G →* MulAut (Multiplicative V))
    (hφ : ∀ g v, (φ g (Multiplicative.ofAdd v)).toAdd=ρ g v)
    (E : Subgroup (Multiplicative V ⋊[φ] G)) [IsElementaryAbelian 2 E]
    (hne : E.map rightHom≠⊥) (hc : Nat.card V≤Nat.card E) :
    IsOffender ρ (E.map rightHom) := by
  have hE : IsElementaryTwo (E.map rightHom) := ⟨hne,IsElementaryAbelian.map rightHom⟩
  exact (EndFieldTransfer.offender_iff_card ρ _ hE).mpr
    (hc.trans (semidirect_commutative_card_le ρ φ hφ E))

end Representation.BinaryOffender
