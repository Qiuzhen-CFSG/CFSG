module

public import Theory.SpecificGroups.Lyons.Atlas111InvolutionCentralizerSetup
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Tactic.Group

/-!
# Double-coset reductions for the concrete Lyons involution subgroup

Since `ab` belongs to the local subgroup and `a` is an involution, closure of a
union of double cosets under right multiplication by `a` implies coverage of
the whole group. The transition hypothesis explicitly includes every middle
factor in the local subgroup; transitions for the representatives alone do
not suffice. No subgroup identification, order or maximality is used.

For separating candidate double cosets, the product `t * (r⁻¹ * t * r)` changes
by conjugation when `r` is replaced by `h * r * k`, provided the certified
local generators commute with `t`. Its order is consequently an invariant.

These are certificate reductions, not a completed enumeration: this module
does not provide a finite representative family or assert its existence.

Source for the local words: ATLAS of Finite Group Representations,
`LyG1-max4W1`, preserved with attribution in `Atlas111InvolutionSource/`.
The proofs are elementary word induction and conjugation identities.
-/

namespace Lyons.SimplicityCertificate

/-- Product of the local involution candidate with its conjugate by `r`. -/
@[expose] public def involutionDoubleCosetProduct (r : LyonsGroup) : LyonsGroup :=
  involutionLocalT * (r⁻¹ * involutionLocalT * r)

/-- Local changes of representative conjugate the involution product. -/
public theorem involutionDoubleCosetProduct_mul_local
    (hcomm : involutionLocalB * involutionLocalT = involutionLocalT * involutionLocalB)
    (r h k : LyonsGroup) (hh : h ∈ involutionLocalSubgroup)
    (hk : k ∈ involutionLocalSubgroup) :
    involutionDoubleCosetProduct (h * r * k) = k⁻¹ * involutionDoubleCosetProduct r * k := by
  have hc (x : LyonsGroup) (hx : x ∈ involutionLocalSubgroup) :
      x * involutionLocalT = involutionLocalT * x :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (involutionLocalSubgroup_le_centralizer hcomm hx)
  have hh' : h⁻¹ * involutionLocalT * h = involutionLocalT := by
    rw [mul_assoc, ← hc h hh, inv_mul_cancel_left]
  have hk' : involutionLocalT * k⁻¹ = k⁻¹ * involutionLocalT :=
    (hc k⁻¹ (involutionLocalSubgroup.inv_mem hk)).symm
  have he : (h * r * k)⁻¹ * involutionLocalT * (h * r * k) =
      k⁻¹ * (r⁻¹ * involutionLocalT * r) * k := by
    calc
      _ = k⁻¹ * r⁻¹ * (h⁻¹ * involutionLocalT * h) * r * k := by group
      _ = _ := by rw [hh']; group
  simp only [involutionDoubleCosetProduct, he, ← mul_assoc, hk']

/-- The order of the involution product is constant on each double coset. -/
public theorem involutionDoubleCosetProduct_order_mul_local
    (hcomm : involutionLocalB * involutionLocalT = involutionLocalT * involutionLocalB)
    (r h k : LyonsGroup) (hh : h ∈ involutionLocalSubgroup)
    (hk : k ∈ involutionLocalSubgroup) :
    orderOf (involutionDoubleCosetProduct (h * r * k)) =
      orderOf (involutionDoubleCosetProduct r) := by
  rw [involutionDoubleCosetProduct_mul_local hcomm r h k hh hk]
  apply SemiconjBy.orderOf_eq k
  change k * (k⁻¹ * involutionDoubleCosetProduct r * k) =
    involutionDoubleCosetProduct r * k
  group

/-- Different product orders certify different double cosets. -/
public theorem involutionDoubleCoset_ne_of_product_order_ne
    (hcomm : involutionLocalB * involutionLocalT = involutionLocalT * involutionLocalB)
    (r s : LyonsGroup)
    (hne : orderOf (involutionDoubleCosetProduct s) ≠
      orderOf (involutionDoubleCosetProduct r)) :
    ¬ ∃ h ∈ involutionLocalSubgroup, ∃ k ∈ involutionLocalSubgroup,
      s = h * r * k := by
  rintro ⟨h, hh, k, hk, rfl⟩
  exact hne (involutionDoubleCosetProduct_order_mul_local hcomm r h k hh hk)

/-- A family containing the identity covers the group if it is closed under
`r i * h * a` for every local middle factor `h`. Only this one outer generator
is required, since `b = a * involutionLocalA` and `a⁻¹ = a`. -/
public theorem involutionLocal_doubleCoset_cover_of_middle_transitions
    {ι : Type*} (r : ι → LyonsGroup) (initial : ι) (hinitial : r initial = 1)
    (hstep : ∀ (i : ι) (h : involutionLocalSubgroup),
      ∃ j, ∃ k ∈ involutionLocalSubgroup, ∃ l ∈ involutionLocalSubgroup,
        r i * h.val * generatorA = k * r j * l)
    (g : LyonsGroup) :
    ∃ i, ∃ h ∈ involutionLocalSubgroup, ∃ k ∈ involutionLocalSubgroup,
      g = h * r i * k := by
  let P (x : LyonsGroup) :=
    ∃ i, ∃ h ∈ involutionLocalSubgroup, ∃ k ∈ involutionLocalSubgroup,
      x = h * r i * k
  have hlocal {x y : LyonsGroup} (hx : P x) (hy : y ∈ involutionLocalSubgroup) :
      P (x * y) := by
    obtain ⟨i, h, hh, k, hk, rfl⟩ := hx
    exact ⟨i, h, hh, k * y, involutionLocalSubgroup.mul_mem hk hy, mul_assoc _ _ _⟩
  have ha {x : LyonsGroup} (hx : P x) : P (x * generatorA) := by
    obtain ⟨i, h, hh, k, hk, rfl⟩ := hx
    obtain ⟨j, l, hl, m, hm, he⟩ := hstep i ⟨k, hk⟩
    refine ⟨j, h * l, involutionLocalSubgroup.mul_mem hh hl, m, hm, ?_⟩
    simpa only [mul_assoc] using congrArg (h * ·) he
  have hainv : generatorA⁻¹ = generatorA :=
    inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using generatorA_sq)
  have hb : generatorB = generatorA * involutionLocalA := by
    rw [involutionLocalA_eq, ← mul_assoc, ← pow_two, generatorA_sq, one_mul]
  have hg : g ∈ Subgroup.closure {generatorA, generatorB} := by
    rw [OrderCertificate.closure_generators]
    trivial
  change P g
  induction hg using Subgroup.closure_induction_right with
  | one =>
    exact ⟨initial, 1, involutionLocalSubgroup.one_mem, 1,
      involutionLocalSubgroup.one_mem, by simp only [hinitial, mul_one]⟩
  | mul_right x _ y hy ih =>
    rcases hy with rfl | hy
    · exact ha ih
    · rcases hy with rfl
      rw [hb, ← mul_assoc]
      exact hlocal (ha ih) involutionLocalA_mem
  | mul_inv_cancel x _ y hy ih =>
    rcases hy with rfl | hy
    · rw [hainv]
      exact ha ih
    · rcases hy with rfl
      rw [hb, mul_inv_rev, hainv, ← mul_assoc]
      exact ha (hlocal ih (involutionLocalSubgroup.inv_mem involutionLocalA_mem))

end Lyons.SimplicityCertificate
