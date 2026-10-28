module
public import Theory.GroupAction.BinaryWreathVectorOrbits

/-!
# Invariant subgroups and plane fixers of the binary wreath module

A nonidentity vector in an invariant subgroup has a nontrivial one-plane
commutator. Transitivity on supported vectors then supplies both coordinate
planes, proving irreducibility. The pointwise fixer of one plane is exactly
the other SL₂(2) factor, whose order is six. Only the four-element plane and
the six-element factor are checked by finite kernel reduction.

These results identify the original second factor and bound the core
centralizer in Aschbacher--Smith 14.6.17, printed pp.1035--1036.
-/

public section
open Subgroup
namespace BinaryWreathPointStabilizer
attribute [local instance] FourGroupMatrixCoordinates.naturalAction
attribute [local instance] RegularWreathProduct.functionModule

private instance planeMovedDecidable (v : Plane) : Decidable (∃ a : MatrixActor, a • v ≠ v) :=
  Fintype.decidableExistsFintype

private theorem plane_moved : ∀ v : Plane, v ≠ 1 → ∃ a : MatrixActor, a • v ≠ v := by
  decide +kernel

/-- The natural binary wreath module has no proper nonzero invariant subgroup. -/
theorem invariant_subgroup_eq_bot_or_top (B : Subgroup Vector)
    (hB : ∀ a : Actor, ∀ v ∈ B, a • v ∈ B) : B = ⊥ ∨ B = ⊤ := by
  classical
  by_cases hb : B = ⊥
  · exact Or.inl hb
  obtain ⟨v,hv,hvn⟩ := B.bot_or_exists_ne_one.resolve_left hb
  have hi : ∃ i : Index, v i ≠ 1 := by
    by_contra hn
    push Not at hn
    exact hvn (funext hn)
  obtain ⟨i,hi⟩ := hi
  obtain ⟨a,ha⟩ := plane_moved (v i) hi
  let g : Actor := ⟨fun k => if k = i then a else 1,1⟩
  let w : Vector := v⁻¹ * (g • v)
  have hw : w ∈ B := B.mul_mem (B.inv_mem hv) (hB g v hv)
  have hws : Supported i w := by
    intro k hk
    change (v k)⁻¹ * ((if k = i then a else 1) • v (1⁻¹ * k)) = 1
    simp only [if_neg hk,inv_one,one_mul,one_smul,inv_mul_cancel]
  have hwn : w ≠ 1 := by
    intro he
    have hh := congrFun he i
    change (v i)⁻¹ * ((if i = i then a else 1) • v (1⁻¹ * i)) = 1 at hh
    simp only [ite_true,inv_one,one_mul] at hh
    exact ha (inv_mul_eq_one.mp hh).symm
  have hs (j : Index) (t : Vector) (ht : Supported j t) : t ∈ B := by
    by_cases ht1 : t = 1
    · exact ht1 ▸ B.one_mem
    obtain ⟨g,hg⟩ := supported_transitive hws ht hwn ht1
    exact hg ▸ hB g w hw
  refine Or.inr (top_unique ?_)
  intro t _
  let x : Vector := fun k => if k = 1 then t k else 1
  let y : Vector := fun k => if k = 1 then 1 else t k
  have hx : Supported 1 x := fun k hk => if_neg hk
  let j : Index := Multiplicative.ofAdd (1 : ZMod 2)
  have hy : Supported j y := by
    intro k hk
    have hk1 : k = 1 := by
      have hh : ∀ k : Index, k ≠ Multiplicative.ofAdd (1 : ZMod 2) → k = 1 := by decide
      exact hh k hk
    exact if_pos hk1
  have he : x * y = t := by
    funext k
    by_cases hk : k = 1 <;> simp [x,y,hk]
  exact he ▸ B.mul_mem (hs 1 x hx) (hs j y hy)
end BinaryWreathPointStabilizer

namespace BinaryWreathPointStabilizer
attribute [local instance] FourGroupMatrixCoordinates.naturalAction
attribute [local instance] RegularWreathProduct.functionModule

/-- The other direct factor is the pointwise fixer of the first coordinate plane. -/
theorem mem_secondFactor_iff (i : Index) (a : Actor) :
    a ∈ secondFactor i ↔ ∀ v : Vector, Supported i v → a • v = v := by
  constructor
  · exact fun ha v hv => secondFactor_le_stabilizer hv ha
  · intro hf
    let z : Plane := Multiplicative.ofAdd (fun _ => (1 : ZMod 2))
    let v : Vector := fun k => if k = i then z else 1
    have hv : Supported i v := fun k hk => if_neg hk
    have hvn : v ≠ 1 := by
      intro he
      have hh := congrFun (congrArg Multiplicative.toAdd (congrFun he i)) (0 : Fin 2)
      norm_num [v,z] at hh
    have hshift := fixed_no_shift hv hvn a (hf v hv)
    refine ⟨hshift,?_⟩
    let := FourGroupMatrixCoordinates.naturalAction_faithful
    apply (FaithfulSMul.eq_of_smul_eq_smul (α := Plane))
    intro w
    have hh := congrFun (hf (fun k => if k = i then w else 1)
      (fun k hk => if_neg hk)) i
    change a.left i • (if a.right⁻¹ * i = i then w else 1) = (if i = i then w else 1) at hh
    simpa only [hshift,inv_one,one_mul,ite_true,one_smul] using hh

private instance factorActorFintype : Fintype Actor := Fintype.ofEquiv ((Index → MatrixActor) × Index)
  (RegularWreathProduct.equivProd MatrixActor Index).symm
private instance secondFactorDecidable (i : Index) : DecidablePred (· ∈ secondFactor i) :=
  fun a => inferInstanceAs (Decidable (a.right = 1 ∧ a.left i = 1))

private theorem secondFactor_card_check : ∀ i : Index, Fintype.card (secondFactor i) = 6 := by
  decide +kernel

/-- Each literal direct factor has the order of SL₂(2). -/
theorem card_secondFactor (i : Index) : Nat.card (secondFactor i) = 6 := by
  rw [Nat.card_eq_fintype_card]
  exact secondFactor_card_check i

end BinaryWreathPointStabilizer

public section
namespace BinaryWreathPointStabilizer
attribute [local instance] FourGroupMatrixCoordinates.naturalAction
attribute [local instance] RegularWreathProduct.functionModule

private theorem plane_fixed_eq_one : ∀ v : Plane,
    (∀ a : MatrixActor, a • v = v) → v = 1 := by decide +kernel

/-- The full natural wreath actor fixes only the identity vector. -/
theorem fixed_vector_eq_one (v : Vector) (hv : ∀ a : Actor, a • v = v) : v = 1 := by
  funext i
  apply plane_fixed_eq_one (v i)
  intro a
  have he := congrFun (hv ⟨fun _ => a,1⟩) i
  simpa only [RegularWreathProduct.functionModule_smul_apply,inv_one,one_mul] using he

end BinaryWreathPointStabilizer
