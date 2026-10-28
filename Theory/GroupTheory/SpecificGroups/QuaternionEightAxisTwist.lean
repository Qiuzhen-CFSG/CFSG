module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.Fintype.Prod

/-!
# An axis-fixing twist of a quaternion outer involution

For an outer involution `e` of Q₈, an inner twist `e * conj b` fixes every
`x` whose displacement `x⁻¹ * e x` is central, and does not commute with `e`.
The twist is the order-four rotation in the dihedral automorphism group
containing `e` and the inner automorphisms.

We encode automorphisms by their two generator images and prove the selection
by a kernel-checked finite table. The second theorem transports the result
along a quaternion model. This supplies the local action used to construct a
nontrivial derived square in a quaternion central-product extension.

Source: Janko–Thompson, Math. Z. 113 (1970), §4 case (b)(ii), printed p.391,
with the structural references on p.386. Generator-image encoding follows
`QuaternionEightAut.lean`.
-/

namespace QuaternionGroup
private abbrev Q := QuaternionGroup 2
private def pairMap (p : Q × Q) : Q → Q
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val
private def twist (p : Q × Q) (b : Q) (x : Q) : Q := pairMap p (b*x*b⁻¹)
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem axis_twist_table : ∀ p : Q × Q,
    (∀ x y, pairMap p (x*y) = pairMap p x * pairMap p y) →
    (∀ x, pairMap p (pairMap p x) = x) →
    (¬ ∃ b, ∀ x, pairMap p x = b*x*b⁻¹) →
    ∃ b : Q,
      (¬ ∀ x, pairMap p (twist p b x) = twist p b (pairMap p x)) ∧
      (∀ x, (∀ y, y*(x⁻¹*pairMap p x)=(x⁻¹*pairMap p x)*y) → twist p b x=x) := by
  decide
end QuaternionGroup

namespace QuaternionGroup
private theorem pairMap_aut (e : MulAut Q) (x : Q) :
    pairMap (e (a 1), e (xa 0)) x = e x := by
  cases x with
  | a i =>
    change (e (a 1)) ^ i.val = e (a i)
    rw [← map_pow, a_one_pow, ZMod.natCast_zmod_val]
  | xa i =>
    change e (xa 0) * (e (a 1)) ^ i.val = e (xa i)
    rw [← map_pow, ← map_mul, a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add]

/-- An outer involution of Q₈ has an inner twist fixing its central-displacement
axis and not commuting with the involution. -/
public theorem exists_axis_fixing_twist_two
    (e : MulAut (QuaternionGroup 2)) (he : e^2=1)
    (ho : ¬ ∃ b, e = MulAut.conj b) :
    ∃ b : QuaternionGroup 2, ¬ Commute e (e * MulAut.conj b) ∧
      ∀ x, x⁻¹*e x ∈ Subgroup.center (QuaternionGroup 2) → (e * MulAut.conj b) x = x := by
  have hm : ∀ x y : Q, pairMap (e (a 1), e (xa 0)) (x*y) =
      pairMap (e (a 1), e (xa 0)) x * pairMap (e (a 1), e (xa 0)) y := by
    simp only [pairMap_aut, map_mul, implies_true]
  have hi : ∀ x : Q, pairMap (e (a 1), e (xa 0))
      (pairMap (e (a 1), e (xa 0)) x) = x := by
    intro x
    simpa only [pairMap_aut, pow_two, MulAut.mul_apply, MulAut.one_apply] using
      DFunLike.congr_fun he x
  have hn : ¬ ∃ b : Q, ∀ x, pairMap (e (a 1), e (xa 0)) x = b*x*b⁻¹ := by
    rintro ⟨b,hb⟩
    exact ho ⟨b, MulEquiv.ext (by simpa only [pairMap_aut, MulAut.conj_apply] using hb)⟩
  obtain ⟨b, hb, hx⟩ := axis_twist_table (e (a 1), e (xa 0)) hm hi hn
  refine ⟨b, fun hc => hb ?_, fun x hxc => ?_⟩
  · intro x
    have hh := DFunLike.congr_fun hc.eq x
    simpa only [MulAut.mul_apply, MulAut.conj_apply, twist, pairMap_aut] using hh
  · simpa only [MulAut.mul_apply, MulAut.conj_apply, twist, pairMap_aut] using
      hx x (by simpa only [pairMap_aut] using Subgroup.mem_center_iff.mp hxc)

/-- The axis-fixing twist transported to an arbitrary quaternion model. -/
public theorem exists_axis_fixing_twist_of_equiv
    {G : Type*} [Group G] (model : G ≃* QuaternionGroup 2)
    (e : MulAut G) (he : e^2=1) (ho : ¬ ∃ b, e = MulAut.conj b) :
    ∃ b : G, ¬ Commute e (e * MulAut.conj b) ∧
      ∀ x, x⁻¹*e x ∈ Subgroup.center G → (e * MulAut.conj b) x = x := by
  let a := MulAut.congr model
  have ha : (a e)^2=1 := by rw [← map_pow, he, map_one]
  have ho' : ¬ ∃ b, a e = MulAut.conj b := by
    rintro ⟨b,hb⟩
    apply ho
    refine ⟨model.symm b, ?_⟩
    ext x
    apply model.injective
    have hh := DFunLike.congr_fun hb (model x)
    simpa [a, MulAut.congr_apply, MulAut.conj_apply] using hh
  obtain ⟨b,hb,hx⟩ := exists_axis_fixing_twist_two (a e) ha ho'
  have hac : a (MulAut.conj (model.symm b)) = MulAut.conj b := by
    ext x
    simp [a, MulAut.congr_apply, MulAut.conj_apply]
  refine ⟨model.symm b, ?_, ?_⟩
  · intro hc
    apply hb
    simpa only [map_mul, hac] using hc.map a
  · intro x hxc
    have hx' : (model x)⁻¹ * (a e) (model x) ∈ Subgroup.center (QuaternionGroup 2) := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      obtain ⟨z,rfl⟩ := model.surjective y
      simpa [a, MulAut.congr_apply] using congrArg model (Subgroup.mem_center_iff.mp hxc z)
    apply model.injective
    have hh := hx (model x) hx'
    simpa [a, MulAut.congr_apply, MulAut.conj_apply] using hh
end QuaternionGroup
