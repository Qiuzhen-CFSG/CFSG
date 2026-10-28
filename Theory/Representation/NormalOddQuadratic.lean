module

public import Theory.Representation.NormalInvariants
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Algebra.CharP.Two

/-!
# Quadratic refinements normalized by an odd normal subgroup

In characteristic two, average a quadratic refinement over a finite group of
odd order. If this group has no fixed vectors, its invariant refinement is
unique: the difference of two refinements with the same polar form is
additive, so its value on the zero average vector is its value on the original
vector. A normalizing isometry must therefore preserve that refinement.

This gives an alternative odd-core argument for the actual orthogonal-case
exclusion in Aschbacher--Smith E.2.7, printed p.220, avoiding the primitive
restriction argument in G.4.9, printed p.341. No perfect-field assumption is
needed for the uniqueness argument.
-/

public noncomputable section

open Subgroup

namespace Representation.NormalOddQuadratic

variable {F G V : Type*} [Field F] [CharP F 2] [Group G]
    [AddCommGroup V] [Module F V]

/-- With no fixed vectors, an odd group has at most one invariant quadratic
refinement of a specified polar form. -/
theorem eq_of_same_polar_of_odd_invariant
    (ρ : Representation F G V) [Finite G] (hodd : Odd (Nat.card G))
    (hfix : invariants ρ = ⊥)
    (Q R : QuadraticForm F V) (hpol : Q.polarBilin = R.polarBilin)
    (hQ : ∀ g v, Q (ρ g v) = Q v) (hR : ∀ g v, R (ρ g v) = R v) : Q = R := by
  classical
  let := Fintype.ofFinite G
  have hc : (Fintype.card G : F) = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_eq_one_of_odd_of_two_eq_zero hodd CharTwo.two_eq_zero
  let D : V →+ F := {
    toFun := fun v => Q v - R v
    map_zero' := by simp
    map_add' := by
      intro x y
      change Q (x+y)-R (x+y) = (Q x-R x)+(Q y-R y)
      rw [QuadraticMap.map_add Q x y,QuadraticMap.map_add R x y]
      simp only [← QuadraticMap.polarBilin_apply_apply, hpol]
      abel }
  have hD (g : G) (v : V) : D (ρ g v) = D v := by
    change Q (ρ g v)-R (ρ g v)=Q v-R v
    rw [hQ,hR]
  apply QuadraticMap.ext
  intro v
  apply sub_eq_zero.mp
  change D v = 0
  have hs : (∑ g : G, ρ g v) ∈ invariants ρ := by
    intro g
    simp only [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => by
      change ρ g (ρ h v)=ρ (g*h) v
      rw [map_mul,Module.End.mul_apply])
  have hz : (∑ g : G, ρ g v) = 0 := by simpa only [hfix,Submodule.mem_bot] using hs
  calc
    D v = ∑ g : G, D (ρ g v) := by
      simp only [hD,Finset.sum_const,Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul F,hc,one_smul]
    _ = D (∑ g : G, ρ g v) := (map_sum D _ _).symm
    _ = 0 := by rw [hz,map_zero]

/-- Averaging over an odd normal subgroup with no fixed vectors constructs a
quadratic refinement invariant under the whole ambient group. -/
theorem exists_invariant_of_odd_normal
    (ρ : Representation F G V) (N : Subgroup G) [N.Normal] [Finite N]
    (hodd : Odd (Nat.card N)) (hfix : invariants (ρ.comp N.subtype) = ⊥)
    (Q₀ : QuadraticForm F V)
    (hpol : ∀ g x y, Q₀.polarBilin (ρ g x) (ρ g y) = Q₀.polarBilin x y) :
    ∃ Q : QuadraticForm F V, Q.polarBilin = Q₀.polarBilin ∧
      ∀ g v, Q (ρ g v) = Q v := by
  classical
  let := Fintype.ofFinite N
  have hc : (Fintype.card N : F) = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact natCast_eq_one_of_odd_of_two_eq_zero hodd CharTwo.two_eq_zero
  let Q : QuadraticForm F V := ∑ n : N, Q₀.comp (ρ n)
  have happ (v : V) : Q v = ∑ n : N, Q₀ (ρ n v) := by
    simp only [Q,sum_apply,QuadraticMap.comp_apply]
  have hp : Q.polarBilin = Q₀.polarBilin := by
    ext x y
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,happ]
    rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
    have ht (n:N) : Q₀ (ρ n (x+y))-Q₀ (ρ n x)-Q₀ (ρ n y)=Q₀.polarBilin x y := by
      simpa only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,map_add] using hpol n x y
    simp only [ht,Finset.sum_const,Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul F,hc,one_smul]
    rfl
  have hQN (a : N) (v : V) : Q (ρ a v)=Q v := by
    rw [happ,happ]
    exact Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun n => by
      change Q₀ (ρ n (ρ a v))=Q₀ (ρ (n*a) v)
      rw [map_mul,Module.End.mul_apply])
  refine ⟨Q,hp,fun g => ?_⟩
  have hpg : (Q.comp (ρ g)).polarBilin = Q.polarBilin := by
    rw [QuadraticMap.polarBilin_comp,hp]
    ext x y
    exact hpol g x y
  have hng (a : N) (v : V) : (Q.comp (ρ g)) (ρ a v)=(Q.comp (ρ g)) v := by
    let b : N := ⟨g*(a:G)*g⁻¹,(inferInstance : N.Normal).conj_mem a a.property g⟩
    have he : g*(a:G)=(b:G)*g := by dsimp [b]; group
    change Q (ρ g (ρ a v))=Q (ρ g v)
    rw [←Module.End.mul_apply,←map_mul,he,map_mul,Module.End.mul_apply]
    exact hQN b (ρ g v)
  have he := eq_of_same_polar_of_odd_invariant (ρ.comp N.subtype) hodd hfix
    (Q.comp (ρ g)) Q hpg hng hQN
  intro v
  exact congrArg (fun R : QuadraticForm F V => R v) he

end Representation.NormalOddQuadratic
