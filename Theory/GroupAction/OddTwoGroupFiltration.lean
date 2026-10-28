module
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Action.Basic

/-!
# Odd actions fixing a two-group filtration

Let a finite group of odd order act by automorphisms on a finite two-group
Q, with subgroups Z≤V. Suppose it fixes Z pointwise, acts trivially on V/Z
in the explicit displacement sense, and acts trivially on Q/V in the same
sense. Then its action on Q is trivial. No characteristic-subgroup,
centrality, or separately chosen invariant-action hypothesis is required.

For a point q whose left discrepancies q⁻¹(a•q) lie in a fixed two-subgroup
N, the discrepancy map from the acting group to N is a homomorphism.
Pointwise fixation gives its multiplication rule in the same order, even
when N is noncommutative. Every image element has order dividing both the
odd acting-group order and a power of two, and hence equals the identity.
Apply this pointwise first to V with N=Z, then to Q with N=V.

This elementary coprime-action argument supplies the ordinary quotient-kernel
step in Stellmacher (8.6), cost-four case. The application uses the actual
next two-core, its module and its central line; the present result is
independent of the graph and classification hypotheses.
-/

namespace MulDistribMulAction

private theorem fixed_of_odd_of_fixed_two_discrepancy
    {A Q : Type*} [Group A] [Finite A] [Group Q] [MulDistribMulAction A Q]
    (hA : Odd (Nat.card A)) (N : Subgroup Q) (hN : IsPGroup 2 N)
    (hfixed : ∀ a : A, ∀ n ∈ N, a • n = n)
    (q : Q) (hdisplacement : ∀ a : A, q⁻¹ * (a • q) ∈ N) :
    ∀ a : A, a • q = q := by
  let displacement : A →* N := {
    toFun := fun a => ⟨q⁻¹ * (a • q),hdisplacement a⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change q⁻¹ * ((a*b) • q) = (q⁻¹ * (a • q)) * (q⁻¹ * (b • q))
      calc
        q⁻¹ * ((a*b) • q) = q⁻¹ * (a • (q * (q⁻¹ * (b • q)))) := by
          rw [mul_inv_cancel_left,mul_smul]
        _ = (q⁻¹ * (a • q)) * (q⁻¹ * (b • q)) := by
          rw [smul_mul',hfixed a _ (hdisplacement b),mul_assoc] }
  intro a
  obtain ⟨k,hk⟩ := hN.exists_orderOf_dvd_pow (displacement a)
  have hoddOrder : orderOf (displacement a) ∣ Nat.card A :=
    (orderOf_map_dvd displacement a).trans (orderOf_dvd_natCard a)
  have horder : orderOf (displacement a) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hA.coprime_two_right.pow_right k) hoddOrder hk
  have hone : displacement a = 1 := orderOf_eq_one_iff.mp horder
  exact (inv_mul_eq_one.mp (congrArg Subtype.val hone)).symm

public theorem trivial_of_odd_of_two_group_filtration
    {A Q : Type*} [Group A] [Group Q] [Finite A] [Finite Q]
    [MulDistribMulAction A Q]
    (hA : Odd (Nat.card A)) (hQ : IsPGroup 2 Q)
    (Z V : Subgroup Q) (hZV : Z ≤ V)
    (hfixedZ : ∀ a : A, ∀ z ∈ Z, a • z = z)
    (hmiddle : ∀ a : A, ∀ v ∈ V, v⁻¹ * (a • v) ∈ Z)
    (htop : ∀ a : A, ∀ q : Q, q⁻¹ * (a • q) ∈ V) :
    ∀ a : A, ∀ q : Q, a • q = q := by
  have hVtwo : IsPGroup 2 V := hQ.to_subgroup V
  have hZtwo : IsPGroup 2 Z := hVtwo.to_le hZV
  have hfixedV : ∀ a : A, ∀ v ∈ V, a • v = v := by
    intro a v hv
    exact fixed_of_odd_of_fixed_two_discrepancy hA Z hZtwo hfixedZ v
      (fun b => hmiddle b v hv) a
  intro a q
  exact fixed_of_odd_of_fixed_two_discrepancy hA V hVtwo hfixedV q
    (fun b => htop b q) a

end MulDistribMulAction
