module

public import Theory.Representation.BinaryPermutation
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.GroupTheory.PGroup
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RepresentationTheory.Intertwining

/-!
# Simple quotients of permutation modules with two-group stabilizers

A two-group fixes a nonzero vector on every nonzero finite-dimensional binary
module. If a transitive permutation action has such a point stabilizer, extend
a fixed vector along its orbit to obtain an equivariant map from the permutation
module. For an irreducible target the nonzero map is surjective.

This is the universal quotient step in the direct binary proof of
Aschbacher–Smith H.6.1, printed p.386, using the twenty-one flags for SL₃(2).
The statements here apply to any actual transitive action with the given
stabilizer; no representation catalogue is assumed.
-/

@[expose] public section

open Representation
namespace BinaryLinearThree.IrreducibleCatalogue

theorem binary_pGroup_fixed_vector
    {G V : Type*} [_root_.Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (ρ : Representation (ZMod 2) G V) (hG : IsPGroup 2 G) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  classical
  let e := (Module.finBasis (ZMod 2) V).equivFun
  let : Finite V := Finite.of_equiv _ e.symm.toEquiv
  let : MulAction G V := {
    smul := fun g v => ρ g v
    one_smul v := by change ρ 1 v = v; simp
    mul_smul g h v := by change ρ (g*h) v = ρ g (ρ h v); rw [map_mul]; rfl }
  have hc : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hd : 2 ∣ Nat.card V := by
    rw [hc]
    exact dvd_pow_self _ (ne_of_gt (Module.finrank_pos (R := ZMod 2) (M := V)))
  have hz : (0 : V) ∈ MulAction.fixedPoints G V := by
    intro g
    change ρ g 0 = 0
    exact map_zero _
  obtain ⟨v,hv,hv0⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hd hz
  exact ⟨v, Ne.symm hv0, hv⟩

theorem irreducible_permutation_quotient
    {G Ω V : Type*} [_root_.Group G] [Fintype Ω]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (τ : G →* Equiv.Perm Ω) (o : Ω)
    (H : Subgroup G) (hH : IsPGroup 2 H)
    (hstab : ∀ g : G, g ∈ H ↔ τ g o = o)
    (htrans : ∀ x : Ω, ∃ g : G, τ g o = x)
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ] :
    ∃ f : Representation.IntertwiningMap ((BinaryPermutation.representation Ω).comp τ) ρ,
      Function.Surjective f := by
  classical
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨v,hv,hfix⟩ := binary_pGroup_fixed_vector (ρ.comp H.subtype) hH
  let lift (x : Ω) : G := Classical.choose (htrans x)
  have hlift (x : Ω) : τ (lift x) o = x := Classical.choose_spec (htrans x)
  let value (x : Ω) : V := ρ (lift x) v
  have hvalue (g : G) (x : Ω) (hg : τ g o = x) : value x = ρ g v := by
    have hm : (lift x)⁻¹ * g ∈ H := by
      rw [hstab, map_mul, map_inv]
      change (τ (lift x)).symm (τ g o) = o
      rw [hg]
      apply (τ (lift x)).injective
      simpa only [Equiv.apply_symm_apply] using (hlift x).symm
    have hh := hfix ⟨(lift x)⁻¹ * g, hm⟩
    change ρ ((lift x)⁻¹ * g) v = v at hh
    have he := congrArg (ρ (lift x)) hh
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at he
    exact he.symm
  have hvalue_o : value o = v := by
    simpa using hvalue 1 o (by simp)
  have hvalue_act (g : G) (x : Ω) : value (τ g x) = ρ g (value x) := by
    have hx : τ (g * lift x) o = τ g x := by
      rw [map_mul]
      change τ g (τ (lift x) o) = τ g x
      rw [hlift]
    rw [hvalue (g * lift x) _ hx, map_mul]
    rfl
  let f : Representation.IntertwiningMap ((BinaryPermutation.representation Ω).comp τ) ρ := {
    toLinearMap := {
      toFun := fun a => ∑ x : Ω, a x • value x
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [mul_smul, Finset.smul_sum] }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro a
      change (∑ x : Ω, a ((τ g).symm x) • value x) =
        ρ g (∑ x : Ω, a x • value x)
      rw [map_sum]
      simp only [map_smul, ← hvalue_act]
      exact (Equiv.sum_comp (τ g)
        (fun x => a ((τ g).symm x) • value x)).symm.trans (by simp) }
  have hf : f (Pi.single o 1) = v := by
    change (∑ x : Ω, (Pi.single o (1 : ZMod 2) : Ω → ZMod 2) x • value x) = v
    simp [hvalue_o]
  refine ⟨f, ?_⟩
  rcases IsIrreducible.surjective_or_eq_zero f with hs | hz
  · exact hs
  · have he := congrArg (fun f => f (Pi.single o 1)) hz
    exact False.elim (hv (hf.symm.trans he))

end BinaryLinearThree.IrreducibleCatalogue
