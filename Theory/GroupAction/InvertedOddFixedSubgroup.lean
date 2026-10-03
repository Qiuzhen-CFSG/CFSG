module
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Action.End

/-!
# An inverted odd actor group fixes an invariant subgroup

Let a finite odd subgroup of an acting group be inverted by an element.
If that element fixes an invariant subgroup pointwise, the entire odd
subgroup fixes it pointwise. Neither faithfulness nor an involution
hypothesis on the inverting element is required.

For an odd-group actor r and a point in the invariant subgroup, applying
the inverter before and after r shows that r and its inverse have the
same effect. Thus r² fixes every point. Squaring is surjective on a finite
odd group, so every actor fixes every point.

This elementary action transfer is used in Stellmacher (10.1), Journal of
Algebra 190 (1997), printed p.63, when a conjugate selected actor is assumed
to lie in the centralizing coatom. The theorem itself is source-neutral.
-/

public theorem inverted_odd_fixes_invariant_subgroup
    {X W : Type*} [Group X] [Group W] [MulDistribMulAction X W]
    (R : Subgroup X) [Finite R] (hodd : Odd (Nat.card R))
    (inverter : X)
    (hinverts : ∀ actor ∈ R, inverter * actor * inverter⁻¹ = actor⁻¹)
    (N : Subgroup W)
    (hstable : ∀ actor ∈ R, ∀ point ∈ N, actor • point ∈ N)
    (hfixed : ∀ point ∈ N, inverter • point = point) :
    ∀ actor ∈ R, ∀ point ∈ N, actor • point = point := by
  have hsquare (actor : R) (point : W) (hpoint : point ∈ N) :
      ((actor : X) ^ 2) • point = point := by
    have hinvfix : inverter⁻¹ • point = point := by
      have hh := congrArg (fun value : W => inverter⁻¹ • value) (hfixed point hpoint)
      simpa using hh.symm
    have heq : (actor : X)⁻¹ • point = (actor : X) • point := by
      rw [← hinverts actor actor.property]
      simp only [mul_smul]
      rw [hinvfix]
      exact hfixed _ (hstable actor actor.property point hpoint)
    have hh := congrArg (fun value : W => (actor : X) • value) heq
    simpa [pow_two, mul_smul] using hh.symm
  intro actor hactor point hpoint
  have hsurj : Function.Surjective (fun element : R => element ^ 2) :=
    hodd.coprime_two_right.pow_left_bijective.surjective
  obtain ⟨root, hroot⟩ := hsurj ⟨actor, hactor⟩
  have heq := congrArg (fun element : R => (element : X)) hroot
  change (root : X) ^ 2 = actor at heq
  rw [← heq]
  exact hsquare root point hpoint
