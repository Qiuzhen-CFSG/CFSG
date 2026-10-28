module

public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# Subgroup spaces in a normal elementary abelian module

Subgroups of a normal elementary abelian two-group are binary subspaces of its
additive carrier. Conjugation differences identify the literal group
commutator with the corresponding module commutator. Centralization likewise
puts the subgroup space in the fixed space of the same quotient actor.

The acting quotient is retained through its original surjection and its
centralizer kernel. These identifications apply directly to the local moved
subgroup in Aschbacher--Smith 9.4.1, printed p.735 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace Representation.NormalElementaryQuotient
variable {H Q : Type*} [Group H] [Group Q]
  (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
  (q : H →* Q) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (W : Set H))

def subgroupSpace (A : Subgroup H) : Submodule (ZMod 2) (Additive W) :=
  AddSubgroup.toZModSubmodule 2 (A.subgroupOf W).toAddSubgroup

theorem subgroupSpace_commutator (A B : Subgroup H) (hAW : A ≤ W) :
    subgroupSpace W ⁅A,B⁆ =
      subspaceCommutator (representation W q hq hker) (subgroupSpace W A) (B.map q) := by
  let M := subspaceCommutator (representation W q hq hker) (subgroupSpace W A) (B.map q)
  let C := M.toAddSubgroup.toSubgroup'.map W.subtype
  have hcW : ⁅A,B⁆ ≤ W := (commutator_mono hAW le_top).trans (commutator_le_left W ⊤)
  have hcomm : ⁅A,B⁆ ≤ C := by
    apply commutator_le.mpr
    intro v hv x hx
    refine ⟨⟨⁅v,x⁆,hcW (commutator_mem_commutator hv hx)⟩,?_,rfl⟩
    change Additive.ofMul (⟨⁅v,x⁆,_⟩ : W) ∈ M
    rw [vector_commutator W q hq hker ⟨v,hAW hv⟩ x]
    apply M.neg_mem_iff.mp
    rw [neg_sub]
    exact Submodule.subset_span ⟨_,mem_map_of_mem q hx,Additive.ofMul ⟨v,hAW hv⟩,hv,rfl⟩
  apply le_antisymm
  · intro v hv
    change (v.toMul:H) ∈ ⁅A,B⁆ at hv
    obtain ⟨u,hu,he⟩ := hcomm hv
    have he' : u = v.toMul := Subtype.ext he
    change Additive.ofMul u ∈ M at hu
    simpa only [he',ofMul_toMul] using hu
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,⟨x,hx,rfl⟩,v,hv,rfl⟩
    apply (subgroupSpace W ⁅A,B⁆).neg_mem_iff.mp
    rw [neg_sub]
    have he := vector_commutator W q hq hker v.toMul x
    simp only [ofMul_toMul] at he
    rw [← he]
    exact commutator_mem_commutator hv hx

omit [W.Normal] in
theorem subgroupSpace_mono {A B : Subgroup H} (hAB : A ≤ B) :
    subgroupSpace W A ≤ subgroupSpace W B := fun _ hv => hAB hv

theorem subgroupSpace_fixed_of_centralizes (A B : Subgroup H)
    (hc : B ≤ centralizer (A : Set H)) :
    subgroupSpace W A ≤ fixedSpace (representation W q hq hker) (B.map q) := by
  intro v hv b
  obtain ⟨g,hg,hgb⟩ := b.property
  change representation W q hq hker (b : Q) v = v
  rw [←hgb]
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [representation_apply,←hc hg v.toMul hv,mul_inv_cancel_right]
end Representation.NormalElementaryQuotient
