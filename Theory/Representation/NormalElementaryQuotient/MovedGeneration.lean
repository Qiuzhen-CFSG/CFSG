module
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
/-!
# Lifting moved-plus-fixed generation to original subgroups

A genuine additive generation identity in the original centralizer quotient
lifts to the literal subgroup commutator. A fixed summand centralizing the
chosen actor and the residual is absorbed into the prescribed alpha subgroup.
No direct sum or complement is assumed. The E.2.3 pair and solvable source
consumers supply the additive generation identity from their actual modules.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {G H : Type*} [Group G] [Group H]
theorem le_commutator_sup_fixed_of_generation
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q) (hker : q.ker = centralizer (U : Set G))
    (A X E : Subgroup G) (Y : Subgroup H)
    (hJY : A.map q ≤ Y) (hRY : X.map q ≤ Y)
    (hs : subspaceCommutator (representation U q hq hker) ⊤ (X.map q) ⊔
      fixedSpace (representation U q hq hker) Y = ⊤)
    (hfix : U ⊓ centralizer (A : Set G) ≤ E) :
    U ≤ (⁅U,X⁆ : Subgroup G) ⊔ (E ⊓ centralizer (X : Set G)) := by
  let α := representation U q hq hker
  intro x hx
  have hv : Additive.ofMul (⟨x,hx⟩ : U) ∈
      subspaceCommutator α ⊤ (X.map q) ⊔ fixedSpace α Y := hs.symm ▸ Submodule.mem_top
  obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hv
  have ha' : (a.toMul : G) ∈ (⁅U,X⁆ : Subgroup G) := by
    change a ∈ NormalElementaryQuotient.commutatorSpace U X
    rwa [NormalElementaryQuotient.commutatorSpace_eq U q hq hker]
  have hbJ := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker
    A b).mp (fun a => hb ⟨a,hJY a.property⟩)
  have hbR := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker
    X b).mp (fun a => hb ⟨a,hRY a.property⟩)
  have he' := congrArg (fun v : Additive U => (v.toMul:G)) he
  change (a.toMul:G) * (b.toMul:G) = x at he'
  rw [← he']
  exact mul_mem_sup ha' ⟨hfix ⟨b.toMul.property,hbJ⟩,hbR⟩
end Representation.NormalElementaryQuotient
