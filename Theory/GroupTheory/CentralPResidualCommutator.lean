module

public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Central commutators with p-perfect subgroups

If X is p-perfect and [X,b] lies in a central p-subgroup N of X, then b
centralizes X. Centrality makes x ↦ [x,b] a homomorphism X → N, and
p-perfectness kills that homomorphism. Normality of X in the ambient group
is not required.

Source: the residual centralization step of Aschbacher–Smith,
*The Classification of Quasithin Groups*, B.7.2, printed p.119.
-/

public section

open Subgroup
open scoped commutatorElement

/-- A p-perfect subgroup cannot have a nontrivial central p-valued commutator map. -/
theorem Subgroup.commute_of_central_p_commutator_of_isPPerfect {G : Type*} [Group G]
    {p : ℕ} [Fact p.Prime] (X : Subgroup G) (N : Subgroup X)
    (hX : IsPPerfect p X) (hp : IsPGroup p N) (hc : N ≤ center X)
    (b : G) (hb : ∀ x : X, ⁅(x : G), b⁆ ∈ N.map X.subtype) :
    ∀ x ∈ X, Commute b x := by
  have hmem (x : X) : ⁅(x : G), b⁆ ∈ X := map_subtype_le _ (hb x)
  have hN (x : X) : (⟨⁅(x : G), b⁆, hmem x⟩ : X) ∈ N := by
    obtain ⟨z, hz, he⟩ := hb x
    have he' : z = ⟨⁅(x : G), b⁆, hmem x⟩ := Subtype.ext he
    exact he' ▸ hz
  let f : X →* N := {
    toFun x := ⟨⟨⁅(x : G), b⁆, hmem x⟩, hN x⟩
    map_one' := by apply Subtype.ext; apply Subtype.ext; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      apply Subtype.ext
      change ⁅(x : G) * (y : G), b⁆ = ⁅(x : G), b⁆ * ⁅(y : G), b⁆
      have hxy := congrArg Subtype.val (mem_center_iff.mp (hc (hN y)) x)
      change (x : G) * ⁅(y : G), b⁆ = ⁅(y : G), b⁆ * (x : G) at hxy
      rw [commutatorElement_mul_left_eq_conj_mul, hxy, mul_inv_cancel_right]
      exact congrArg Subtype.val (mem_center_iff.mp (hc (hN x)) ⟨⁅(y : G), b⁆, hmem y⟩) }
  have he := hX.hom_eq_one_of_isPGroup hp f
  intro x hx
  have hx1 := congrArg (fun ff : X →* N => ((ff ⟨x,hx⟩ : N) : G)) he
  change ⁅x, b⁆ = 1 at hx1
  exact (commutatorElement_eq_one_iff_mul_comm.mp hx1).symm
