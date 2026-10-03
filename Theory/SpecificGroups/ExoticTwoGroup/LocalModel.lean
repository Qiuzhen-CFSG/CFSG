module

public import Theory.SpecificGroups.ExoticTwoGroup.Presentation
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Tactic.NormNum

/-!
# A finite model for the exotic two-group

The group is `((C₄ × C₄) ⋊ (C₂ × C₂)) ⋊ (C₂ × C₂)`.
The inner actors are the displayed linear transformations of the two
C₄ coordinates. The outer actors swap both pairs of coordinates and send
`a,b,g₁,g₂` to `a⁻¹,b⁻¹,ag₁,bg₂`, respectively. Their action laws are
finite identities checked by the kernel. The resulting group has 256
coordinates and satisfies the six-generator presentation.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.4(c), p.386.
This construction supplies the concrete side of the local computations on
p.396; identification of an arbitrary presentation is a separate theorem.
-/

namespace ExoticTwoGroup.LocalModel
public abbrev C4 := Multiplicative (ZMod 4)
public abbrev C2 := Multiplicative (ZMod 2)
public abbrev Base := C4 × C4
public abbrev Actor := C2 × C2

@[expose] public def uAct (x : Base) : Base :=
  (Multiplicative.ofAdd (-x.1.toAdd + 2*x.2.toAdd), x.2⁻¹)
@[expose] public def vAct (x : Base) : Base :=
  (x.1⁻¹, Multiplicative.ofAdd (2*x.1.toAdd - x.2.toAdd))
@[expose] public def innerTwist (c : Actor) (x : Base) : Base :=
  let y := if c.2 = 1 then x else vAct x
  if c.1 = 1 then y else uAct y
private theorem inner_involutive : ∀ c : Actor, ∀ x : Base,
    innerTwist c (innerTwist c x) = x := by decide +kernel
private theorem inner_mul : ∀ c : Actor, ∀ x y : Base,
    innerTwist c (x*y) = innerTwist c x * innerTwist c y := by decide +kernel

@[expose] public def innerAction : Actor →* MulAut Base where
  toFun c := {
    toFun := innerTwist c
    invFun := innerTwist c
    left_inv := by exact inner_involutive c
    right_inv := by exact inner_involutive c
    map_mul' := by exact inner_mul c }
  map_one' := by
    apply MulEquiv.ext
    exact (by decide : ∀ x : Base, innerTwist 1 x = x)
  map_mul' c d := by
    apply MulEquiv.ext
    exact (by decide : ∀ c d : Actor, ∀ x : Base,
      innerTwist (c*d) x = innerTwist c (innerTwist d x)) c d
public abbrev Core := SemidirectProduct Base Actor innerAction
public instance : Fintype Core := Fintype.ofEquiv (Base × Actor) SemidirectProduct.equivProd.symm

@[expose] public def zAct (x : Core) : Core :=
  let k : ZMod 4 := x.right.1.toAdd.val
  let l : ZMod 4 := x.right.2.toAdd.val
  ⟨(Multiplicative.ofAdd (-x.left.1.toAdd + k + 2*k*l),
    Multiplicative.ofAdd (-x.left.2.toAdd + l + 2*k*l)), x.right⟩
@[expose] public def tAct (x : Core) : Core := ⟨x.left.swap, x.right.swap⟩
@[expose] public def outerTwist (c : Actor) (x : Core) : Core :=
  let y := if c.2 = 1 then x else zAct x
  if c.1 = 1 then y else tAct y
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem outer_mul : ∀ c : Actor, ∀ x y : Core,
    outerTwist c (x*y) = outerTwist c x * outerTwist c y := by decide +kernel
private theorem outer_involutive : ∀ c : Actor, ∀ x : Core,
    outerTwist c (outerTwist c x) = x := by decide +kernel

@[expose] public def outerAction : Actor →* MulAut Core where
  toFun c := {
    toFun := outerTwist c
    invFun := outerTwist c
    left_inv := by exact outer_involutive c
    right_inv := by exact outer_involutive c
    map_mul' := by exact outer_mul c }
  map_one' := by
    apply MulEquiv.ext
    exact (by decide : ∀ x : Core, outerTwist 1 x = x)
  map_mul' c d := by
    apply MulEquiv.ext
    exact (by decide +kernel : ∀ c d : Actor, ∀ x : Core,
      outerTwist (c*d) x = outerTwist c (outerTwist d x)) c d
public abbrev Model := SemidirectProduct Core Actor outerAction
public instance : Fintype Model := Fintype.ofEquiv (Core × Actor) SemidirectProduct.equivProd.symm

@[expose] public def a : Model := ⟨⟨(Multiplicative.ofAdd 1,1),1⟩,1⟩
@[expose] public def b : Model := ⟨⟨(1,Multiplicative.ofAdd 1),1⟩,1⟩
@[expose] public def g₁ : Model := ⟨⟨1,(Multiplicative.ofAdd 1,1)⟩,1⟩
@[expose] public def g₂ : Model := ⟨⟨1,(1,Multiplicative.ofAdd 1)⟩,1⟩
@[expose] public def t : Model := ⟨1,(Multiplicative.ofAdd 1,1)⟩
@[expose] public def z₀ : Model := ⟨1,(1,Multiplicative.ofAdd 1)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
public theorem normal_form : ∀ x : Model,
  x = a ^ x.left.left.1.toAdd.val * b ^ x.left.left.2.toAdd.val *
    g₁ ^ x.left.right.1.toAdd.val * g₂ ^ x.left.right.2.toAdd.val *
    t ^ x.right.1.toAdd.val * z₀ ^ x.right.2.toAdd.val := by decide +kernel

public theorem card_model : Nat.card Model = 256 := by
  rw [SemidirectProduct.card, SemidirectProduct.card]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card, Base, Actor, C4, C2]

private theorem generate : Subgroup.closure ({a,b,g₁,g₂,t,z₀} : Set Model) = ⊤ := by
  apply top_unique
  intro x _
  rw [normal_form x]
  repeat' apply Subgroup.mul_mem
  all_goals
    apply Subgroup.pow_mem
    exact Subgroup.subset_closure (by simp)

/-- The concrete coordinate group satisfies all the unchanged relations. -/
@[expose] public def presentation : ExoticTwoGroup.Presentation Model where
  a := a
  b := b
  g₁ := g₁
  g₂ := g₂
  t := t
  z₀ := z₀
  a_four := by decide +kernel
  b_four := by decide +kernel
  ab := by change a * b = b * a; decide +kernel
  g₁_two := by decide +kernel
  g₂_two := by decide +kernel
  g₁g₂ := by change g₁ * g₂ = g₂ * g₁; decide +kernel
  g₁_a := by decide +kernel
  g₁_b := by decide +kernel
  g₂_a := by decide +kernel
  g₂_b := by decide +kernel
  t_two := by decide +kernel
  z₀_two := by decide +kernel
  tz₀ := by change t * z₀ = z₀ * t; decide +kernel
  z₀_a := by decide +kernel
  z₀_b := by decide +kernel
  z₀_g₁ := by decide +kernel
  z₀_g₂ := by decide +kernel
  t_a := by decide +kernel
  t_b := by decide +kernel
  t_g₁ := by decide +kernel
  t_g₂ := by decide +kernel
  generate := by exact generate
  card := card_model

end ExoticTwoGroup.LocalModel
