module
public import Theory.Representation.NormalElementaryQuotient
public import Mathlib.GroupTheory.Commutator.Basic
/-!
# Coordinates on the original elementary moved subgroup

The span of the literal quotient-action displacements is precisely the
ambient subgroup commutator, viewed additively. The comparison is an explicit
linear equivalence retaining the original subgroup inclusion. This permits
natural coordinates on an actual moved subspace to be applied to the original
commutator subgroup, without identifying unrelated isomorphic modules.

Source application: Aschbacher–Smith B.6.10 and E.2.3, pp.117 and216–217.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
set_option backward.isDefEq.respectTransparency false
namespace Representation.NormalElementaryQuotient
variable {G H : Type*} [Group G] [Group H]
  (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
  (q : G →* H) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (U : Set G))

def commutatorSpace (X : Subgroup G) : Submodule (ZMod 2) (Additive U) :=
  AddSubgroup.toZModSubmodule 2 ((⁅U,X⁆ : Subgroup G).subgroupOf U).toAddSubgroup

theorem vector_commutator (v : U) (g : G) :
    Additive.ofMul (⟨⁅(v:G),g⁆,(commutator_le_left U ⊤)
      (commutator_mem_commutator v.property (mem_top g))⟩ : U) =
      Additive.ofMul v - representation U q hq hker (q g) (Additive.ofMul v) := by
  apply Additive.toMul.injective
  rw [toMul_sub,div_eq_mul_inv]
  apply Subtype.ext
  change ⁅(v:G),g⁆ = (v:G)*(((representation U q hq hker (q g)
    (Additive.ofMul v)).toMul:G))⁻¹
  rw [representation_apply]
  simp only [commutatorElement_def,mul_inv_rev,inv_inv,mul_assoc,toMul_ofMul]

theorem commutatorSpace_eq (X : Subgroup G) :
    commutatorSpace U X = subspaceCommutator (representation U q hq hker) ⊤ (X.map q) := by
  let W := subspaceCommutator (representation U q hq hker) ⊤ (X.map q)
  let C := W.toAddSubgroup.toSubgroup'.map U.subtype
  have hcU : ⁅U,X⁆ ≤ U := commutator_le_left _ _
  have hcomm : ⁅U,X⁆ ≤ C := by
    apply commutator_le.mpr
    intro v hv x hx
    refine ⟨⟨⁅v,x⁆,hcU (commutator_mem_commutator hv hx)⟩,?_,rfl⟩
    change Additive.ofMul (⟨⁅v,x⁆,_⟩ : U) ∈ W
    rw [vector_commutator U q hq hker ⟨v,hv⟩ x]
    apply W.neg_mem_iff.mp
    rw [neg_sub]
    exact Submodule.subset_span ⟨_,mem_map_of_mem q hx,Additive.ofMul ⟨v,hv⟩,Submodule.mem_top,rfl⟩
  apply le_antisymm
  · intro v hv
    change (v.toMul:G) ∈ ⁅U,X⁆ at hv
    obtain ⟨u,hu,he⟩ := hcomm hv
    have he' : u = v.toMul := Subtype.ext he
    change Additive.ofMul u ∈ W at hu
    simpa only [he',ofMul_toMul] using hu
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,⟨x,hx,rfl⟩,v,_,rfl⟩
    apply (commutatorSpace U X).neg_mem_iff.mp
    rw [neg_sub]
    have he := vector_commutator U q hq hker v.toMul x
    simp only [ofMul_toMul] at he
    rw [← he]
    exact commutator_mem_commutator v.toMul.property hx

variable (X : Subgroup G) [IsElementaryAbelian 2 (⁅U,X⁆ : Subgroup G)]
noncomputable def commutatorSpaceEquiv :
    Additive (⁅U,X⁆ : Subgroup G) ≃ₗ[ZMod 2] commutatorSpace U X := by
  let f : Additive (⁅U,X⁆ : Subgroup G) →ₗ[ZMod 2] commutatorSpace U X := {
    toFun := fun v => ⟨Additive.ofMul ⟨v.toMul,(commutator_le_left U X) v.toMul.property⟩,v.toMul.property⟩
    map_add' := by intros; rfl
    map_smul' := by
      intro c v
      apply Subtype.ext
      exact map_smul ((inclusion (commutator_le_left U X)).toAdditive.toZModLinearMap 2) c v }
  exact LinearEquiv.ofBijective f ⟨fun a b h => Additive.toMul.injective
    (Subtype.ext (congrArg (fun x => x.val.toMul.val) h)),
    fun v => ⟨Additive.ofMul ⟨v.val.toMul,v.property⟩,rfl⟩⟩

noncomputable def movedEquiv :
    Additive (⁅U,X⁆ : Subgroup G) ≃ₗ[ZMod 2]
      subspaceCommutator (representation U q hq hker) ⊤ (X.map q) :=
  (commutatorSpaceEquiv U X).trans
    (LinearEquiv.ofEq _ _ (commutatorSpace_eq U q hq hker X))

@[simp] theorem movedEquiv_val (v : Additive (⁅U,X⁆ : Subgroup G)) :
    (movedEquiv U q hq hker X v).val =
      Additive.ofMul ⟨v.toMul,(commutator_le_left U X) v.toMul.property⟩ := rfl
end Representation.NormalElementaryQuotient
