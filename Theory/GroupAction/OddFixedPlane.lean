module

public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.PGroup

/-!
# Commuting involutions with distinct fixed lines

Two distinct fixed subgroups of order p in a group of order p² intersect
trivially and generate the group. Commuting automorphisms preserve each
other's fixed subgroups. Their restrictions there are fixed-point-free
involutions, hence inversion; the product therefore inverts the whole group.
The final corollary identifies the product with a marked inversion actor.

The proof needs neither an elementary-abelian hypothesis nor a separate
oddness hypothesis: the stated fixed-subgroup configuration already forces
the conclusion. Source application: GLS4, Chapter 2, Proposition 16.5,
the two-dimensional odd-primary quotient in the field-action argument.
-/

namespace Theory.GroupAction
open Subgroup
variable {V : Type*} [Group V] [Finite V]

private theorem fixed_disjoint_of_prime_card {p : ℕ} (hp : p.Prime)
    (u v : MulAut V) (hv : Nat.card v.fixedSubgroup = p)
    (hne : ¬ v.fixedSubgroup ≤ u.fixedSubgroup) :
    Disjoint u.fixedSubgroup v.fixedSubgroup := by
  have hd := card_dvd_of_le
    (show u.fixedSubgroup ⊓ v.fixedSubgroup ≤ v.fixedSubgroup from inf_le_right)
  rw [hv] at hd
  rcases (Nat.dvd_prime hp).mp hd with h1 | h1
  · exact disjoint_iff.mpr ((u.fixedSubgroup ⊓ v.fixedSubgroup).eq_bot_of_card_eq h1)
  · have he : u.fixedSubgroup ⊓ v.fixedSubgroup = v.fixedSubgroup :=
      eq_of_le_of_card_ge inf_le_right (by rw [h1,hv])
    exact (hne (he ▸ (show u.fixedSubgroup ⊓ v.fixedSubgroup ≤ u.fixedSubgroup from inf_le_left))).elim

private theorem inverts_other_fixed (u v : MulAut V)
    (hv : Function.Involutive v) (hc : Commute u v)
    (hd : Disjoint u.fixedSubgroup v.fixedSubgroup)
    {x : V} (hx : x ∈ u.fixedSubgroup) : v x = x⁻¹ := by
  have hcomm (x : V) : u (v x) = v (u x) :=
    congrArg (fun a : MulAut V => a x) hc.eq
  let f : u.fixedSubgroup →* u.fixedSubgroup :=
    { toFun := fun y => ⟨v y, by
        apply (MulAut.mem_fixedSubgroup _ _).mpr
        rw [hcomm, (MulAut.mem_fixedSubgroup _ _).mp y.property]⟩
      map_one' := Subtype.ext (map_one v)
      map_mul' := fun a b => Subtype.ext (map_mul v (a : V) (b : V)) }
  have hf : MonoidHom.FixedPointFree f := by
    intro y hy
    apply Subtype.ext
    exact disjoint_def.mp hd y.property
      ((MulAut.mem_fixedSubgroup _ _).mpr (congrArg Subtype.val hy))
  have hi : Function.Involutive f := fun y => Subtype.ext (hv y)
  exact congrArg Subtype.val
    (congrFun (hf.coe_eq_inv_of_involutive hi) (⟨x,hx⟩ : u.fixedSubgroup))

/-- On a group of order p², commuting involutions with distinct fixed
subgroups of order p have product equal to inversion. -/
public theorem commuting_fixed_lines_product_inverts {p : ℕ} (hp : p.Prime)
    (hV : Nat.card V = p ^ 2) (u v : MulAut V)
    (hu : Function.Involutive u) (hv : Function.Involutive v) (hc : Commute u v)
    (huC : Nat.card u.fixedSubgroup = p) (hvC : Nat.card v.fixedSubgroup = p)
    (hne : ¬ v.fixedSubgroup ≤ u.fixedSubgroup) (x : V) : (u * v) x = x⁻¹ := by
  let : Fact p.Prime := ⟨hp⟩
  let : CommGroup V := IsPGroup.commGroupOfCardEqPrimeSq hV
  have hd := fixed_disjoint_of_prime_card hp u v hvC hne
  have hs : u.fixedSubgroup ⊔ v.fixedSubgroup = ⊤ := by
    apply eq_top_of_card_eq
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ le_normalizer_of_normal hd,
      huC,hvC,hV,pow_two]
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_sup_of_normal_right.mp (hs.symm ▸ mem_top x)
  have hva : v a = a⁻¹ := inverts_other_fixed u v hv hc hd ha
  have hub : u b = b⁻¹ := inverts_other_fixed v u hu hc.symm hd.symm hb
  change u (v (a * b)) = (a * b)⁻¹
  rw [map_mul, hva, (MulAut.mem_fixedSubgroup _ _).mp hb, map_mul, map_inv,
    (MulAut.mem_fixedSubgroup _ _).mp ha, hub, mul_inv_rev, mul_comm]

/-- Identify the product with any marked actor already known to invert V. -/
public theorem commuting_fixed_lines_product_eq_inversion {p : ℕ} (hp : p.Prime)
    (hV : Nat.card V = p ^ 2) (u v τ : MulAut V)
    (hu : Function.Involutive u) (hv : Function.Involutive v) (hc : Commute u v)
    (huC : Nat.card u.fixedSubgroup = p) (hvC : Nat.card v.fixedSubgroup = p)
    (hne : ¬ v.fixedSubgroup ≤ u.fixedSubgroup) (hτ : ∀ x, τ x = x⁻¹) :
    u * v = τ := by
  ext x
  exact (commuting_fixed_lines_product_inverts hp hV u v hu hv hc huC hvC hne x).trans
    (hτ x).symm

/-- The three marked actors satisfy the literal product identity used in
the odd-primary quotient of the source field-action argument. -/
public theorem inversion_mul_commuting_fixed_lines_eq_one {p : ℕ} (hp : p.Prime)
    (hV : Nat.card V = p ^ 2) (u v τ : MulAut V)
    (hu : Function.Involutive u) (hv : Function.Involutive v) (hc : Commute u v)
    (huC : Nat.card u.fixedSubgroup = p) (hvC : Nat.card v.fixedSubgroup = p)
    (hne : ¬ v.fixedSubgroup ≤ u.fixedSubgroup) (hτ : ∀ x, τ x = x⁻¹) :
    τ * u * v = 1 := by
  rw [mul_assoc, commuting_fixed_lines_product_eq_inversion hp hV u v τ hu hv hc huC hvC hne hτ]
  ext x
  change τ (τ x) = x
  rw [hτ,hτ,inv_inv]

end Theory.GroupAction
