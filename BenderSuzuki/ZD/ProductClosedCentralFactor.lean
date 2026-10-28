module

public import Theory.GroupTheory.Involution.Basic
public import Mathlib.GroupTheory.Subgroup.Center
public import Theory.GroupTheory.Involution.OddKernelProductClosure
public import BenderSuzuki.ZD.ProductClosedCentralFactor.ModelGeometry

/-!
# The product-closure obstruction to a central involution factor

A conjugacy-invariant, product-closed set of involutions cannot lie in a
nontrivial central involution coset of a subgroup whose involutions have
distinct commuting conjugates. Two such conjugates multiply into the subgroup,
whereas product closure puts their product back in the nontrivial coset.

This is the elementary final step of the central-factor elimination in
Aschbacher--Smith, Theorem I.8.2, printed pp. 429--430. The final theorem combines
the proved model geometry and odd-kernel descent, eliminating the extra central
factor from the structural witnesses in GLS, Theorem ZD(b), (c), and (e).
The recognition theorem itself is not needed: its simple Bender subgroup and
central coset are explicit inputs. Product closure is the additional property
established for the tightly embedded involution set in I.8.2.
-/

namespace BenderSuzuki.ZD

open PFAppendixIII

variable {Q : Type*} [Group Q]

private theorem central_translate_mul {u : Q}
    (hu : u ∈ Subgroup.center Q) (hu2 : u ^ 2 = 1) (x y : Q) :
    (u * x) * (u * y) = x * y := by
  calc
    (u * x) * (u * y) = (u * (x * u)) * y := by group
    _ = (u * (u * x)) * y := by rw [Subgroup.mem_center_iff.mp hu x]
    _ = (u * u) * (x * y) := by group
    _ = x * y := by rw [← pow_two, hu2, one_mul]

private theorem conj_central_mul {u : Q}
    (hu : u ∈ Subgroup.center Q) (g x : Q) :
    MulAut.conj g (u * x) = u * MulAut.conj g x := by
  rw [map_mul]
  congr 1
  change g * u * g⁻¹ = u
  rw [Subgroup.mem_center_iff.mp hu g, mul_assoc, mul_inv_cancel, mul_one]

/-- The elementary central-coset obstruction. The geometric premise only
concerns involutions of `X`, and no recognition theorem is used here. -/
public theorem central_coset_false_of_commuting_conjugates
    (Z : Set Q) (hZ : Z.Nonempty)
    (hZsq : ∀ z ∈ Z, z ^ 2 = 1)
    (hconj : ∀ g : Q, ∀ z ∈ Z, MulAut.conj g z ∈ Z)
    (hprod : ∀ a ∈ Z, ∀ b ∈ Z, Commute a b → a ≠ b → a * b ∈ Z)
    (X : Subgroup Q)
    (hgeometry : ∀ i : X, IsInvolution i →
      ∃ g : X, MulAut.conj g i ≠ i ∧ Commute i (MulAut.conj g i))
    (u : Q) (hu : u ∈ Subgroup.center Q) (hu2 : u ^ 2 = 1)
    (huX : u ∉ X)
    (hcoset : ∀ z ∈ Z, ∃ x : X, x ≠ 1 ∧ z = u * (x : Q)) : False := by
  obtain ⟨z, hz⟩ := hZ
  obtain ⟨i, hine, hzi⟩ := hcoset z hz
  have hi2 : i ^ 2 = 1 := by
    apply Subtype.ext
    have hz2 := hZsq z hz
    rw [hzi, pow_two, central_translate_mul hu hu2, ← pow_two] at hz2
    exact hz2
  obtain ⟨g, hgi, hic⟩ := hgeometry i ⟨hine, hi2⟩
  let j : X := MulAut.conj g i
  have hjval : (j : Q) = MulAut.conj (g : Q) (i : Q) := rfl
  have hconjz : MulAut.conj (g : Q) z = u * (j : Q) := by
    rw [hzi, conj_central_mul hu, hjval]
  have hujZ : u * (j : Q) ∈ Z := hconjz ▸ hconj (g : Q) z hz
  have huiZ : u * (i : Q) ∈ Z := hzi ▸ hz
  have hicQ : (i : Q) * (j : Q) = (j : Q) * (i : Q) :=
    congrArg Subtype.val hic.eq
  have hc : Commute (u * (i : Q)) (u * (j : Q)) := by
    change (u * (i : Q)) * (u * (j : Q)) =
      (u * (j : Q)) * (u * (i : Q))
    rw [central_translate_mul hu hu2, central_translate_mul hu hu2, hicQ]
  have hne : u * (i : Q) ≠ u * (j : Q) := by
    intro heq
    exact hgi (Subtype.ext (mul_left_cancel heq).symm)
  have hijZ : (i : Q) * (j : Q) ∈ Z := by
    simpa only [central_translate_mul hu hu2] using hprod _ huiZ _ hujZ hc hne
  obtain ⟨k, _hkne, hk⟩ := hcoset _ hijZ
  apply huX
  have hmem : ((i : Q) * (j : Q)) * (k : Q)⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem i.property j.property) (X.inv_mem k.property)
  simpa only [hk, mul_assoc, mul_inv_cancel, mul_one] using hmem

/-- A surjective image supplies the conjugacy-invariant set needed for the
central-coset obstruction. The only descent input is product closure in the
image; odd-kernel lifting will supply it in the finite-group application. -/
public theorem central_coset_false_of_image_product_closed
    {A : Type*} [Group A] (f : A →* Q) (hf : Function.Surjective f)
    (Z : Set A) (hZ : Z.Nonempty)
    (hZinv : ∀ z ∈ Z, IsInvolution z)
    (hconj : ∀ g : A, ∀ z ∈ Z, MulAut.conj g z ∈ Z)
    (hprod : ∀ a ∈ f '' Z, ∀ b ∈ f '' Z,
      Commute a b → a ≠ b → a * b ∈ f '' Z)
    (X : Subgroup Q)
    (hgeometry : ∀ i : X, IsInvolution i →
      ∃ g : X, MulAut.conj g i ≠ i ∧ Commute i (MulAut.conj g i))
    (u : Q) (hu : u ∈ Subgroup.center Q) (hu2 : u ^ 2 = 1)
    (huX : u ∉ X)
    (hcoset : ∀ z ∈ Z, ∃ x : X, x ≠ 1 ∧ f z = u * (x : Q)) : False := by
  apply central_coset_false_of_commuting_conjugates (f '' Z) (hZ.image f)
    ?_ ?_ hprod X hgeometry u hu hu2 huX ?_
  · rintro _ ⟨z, hz, rfl⟩
    rw [← map_pow, (hZinv z hz).sq_eq_one, map_one]
  · intro g
    obtain ⟨a, rfl⟩ := hf g
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨MulAut.conj a z, hconj a z hz, ?_⟩
    simp only [MulAut.conj_apply, map_mul, map_inv]
  · rintro _ ⟨z, hz, rfl⟩
    exact hcoset z hz

/-- Elimination of the nontrivial central involution factor in the ZD branch
of Aschbacher--Smith I.8.2. A nonempty conjugacy-invariant involution set closed
under products of distinct commuting members cannot map into `u * (X - {1})`
through an odd kernel, when `X` is a simple Bender group and `u` is a central
element of order at most two outside `X`.

Odd-kernel lifting supplies product closure in the image. The concrete Bender
models supply a distinct commuting conjugate of its `X`-component, so the
product belongs both to `X` and to the disjoint coset `u * X`. -/
public theorem central_coset_false_of_odd_kernel
    {A : Type*} [Group A] [Finite A] [Finite Q]
    (f : A →* Q) (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    (Z : Set A) (hZ : Z.Nonempty)
    (hZinv : ∀ z ∈ Z, IsInvolution z)
    (hconj : ∀ g : A, ∀ z ∈ Z, MulAut.conj g z ∈ Z)
    (hprod : ∀ a ∈ Z, ∀ b ∈ Z, Commute a b → a ≠ b → a * b ∈ Z)
    (X : Subgroup Q) (hX : IsSimpleBenderGroup X)
    (u : Q) (hu : u ∈ Subgroup.center Q) (hu2 : u ^ 2 = 1)
    (huX : u ∉ X)
    (hcoset : ∀ z ∈ Z, ∃ x : X, x ≠ 1 ∧ f z = u * (x : Q)) : False := by
  exact central_coset_false_of_image_product_closed f hf Z hZ hZinv hconj
    (Theory.GroupTheory.image_product_closed_of_odd_kernel f hf hker Z hZinv hconj hprod)
    X hX.exists_distinct_commuting_conjugate u hu hu2 huX hcoset

end BenderSuzuki.ZD
