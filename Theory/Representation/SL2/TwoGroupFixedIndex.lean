module
public import Theory.GroupTheory.PResidual.ActionKernel
public import Theory.Representation.FrattiniAction
public import Theory.Representation.SL2.ExtensionFieldDegree

/-!
# The linear field-size bound on a finite two-group section

Residual movement survives on the Frattini quotient. An irreducible binary
section removes the kernel of the marked map onto SL₂, so the existing
field-degree bound applies to any escaping two-subgroup. The equivariant
Frattini quotient cannot increase fixed index, returning the bound to the
original two-group. No elementary or faithful-action assumption is imposed
on that original group.

Source: DGS, *Groups and Graphs* (1985), 5.7 and its use in 8.4, pp.108,138;
Niles, *Pushing-up in finite groups* (1979), Lemma 4.3.
`RadiusThreeResidualApplication` gives the original graph-section consumer.
-/

public noncomputable section
namespace Representation.SL2
open Subgroup BinaryOffender BinaryFixedPoints
open scoped MatrixGroups IsMulCommutative
variable {D X K : Type*} [Group D] [Finite D] [Group X] [Finite X]
    [Field K] [Finite K] [CharP K 2]

/-- The field order bounds the fixed index of an escaping two-subgroup
on a two-group moved by the residual. Neither the action nor its Frattini
action is assumed faithful; the kernel of the marked SL₂ map is a two-group. -/
theorem twoGroup_fixedIndex_lower_of_residual_moves
    (π : D →* SL(2,K)) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (hp : IsPGroup 2 X) (α : D →* MulAut X)
    (hr : ¬ pResidual 2 D ≤ α.ker)
    (A : Subgroup D) (hA : IsPGroup 2 A) (hne : A.map π ≠ ⊥)
    {n : ℕ} (hn : 1 < n) (hK : Nat.card K = 2^n) :
    let _ := MulDistribMulAction.compHom X (α.comp A.subtype)
    Nat.card K ≤ (FixedPoints.subgroup A X).index := by
  let _ := MulDistribMulAction.compHom X (α.comp A.subtype)
  let : Fact (IsPGroup 2 X) := ⟨hp⟩
  let Y := X ⧸ frattini X
  let : IsElementaryAbelian 2 Y := isElementaryAbelian_quotient_frattini
  let β := (quotientAut (frattini X)).comp α
  let ρ := Representation.FrattiniAction.ofAutomorphismHom β
  have hβ := MonoidHom.residual_not_le_frattini_action_kernel hp α hr
  have hmove : fixedSpace ρ (pResidual 2 D) ≠ ⊤ := by
    intro he
    apply hβ
    intro r hr
    apply MulEquiv.ext
    intro x
    have hx : Additive.ofMul x ∈ fixedSpace ρ (pResidual 2 D) := he ▸ Submodule.mem_top
    exact congrArg Additive.toMul (hx ⟨r,hr⟩)
  have hl := extension_fixedCodim_lower π hπ hk ρ hmove A (hA.map π) hne hn hK
  let τ := ρ.comp A.subtype
  let := action τ
  let f : X →* Multiplicative (Additive Y) := {
    toFun x := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (frattini X) x))
    map_one' := (QuotientGroup.mk' (frattini X)).map_one
    map_mul' := (QuotientGroup.mk' (frattini X)).map_mul }
  have heq (a : A) (x : X) : f (a • x) = a • f x := by
    change QuotientGroup.mk' (frattini X) (α a.val x) =
      quotientAut (frattini X) (α a.val) (QuotientGroup.mk' (frattini X) x)
    rw [quotientAut_apply_mk]
  have hi : fixedIndex τ ≤ (FixedPoints.subgroup A X).index :=
    fixedPoints_index_le_of_surjective_equivariant f
      (QuotientGroup.mk'_surjective (frattini X)) heq
  rw [Representation.FrattiniAction.fixedIndex_eq_two_pow_fixedCodim ρ A] at hi
  rw [hK]
  exact (Nat.pow_le_pow_right (by decide) hl).trans hi

end Representation.SL2
