module
public import Theory.GroupTheory.ElementaryQuotientCocycles
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Involution fusion through two elementary layers

An involutory action with square-root fixed subgroup on an elementary two-group
has every cocycle a coboundary. Apply this first in a quotient and then in its
elementary kernel. For a literal conjugation action, the resulting coboundary
is precisely a conjugator for every involution in the same coset.

Source application: Aschbacher–Smith, Exercise 2.8 and Lemma 2.4.12(2),
printed p.532 of the combined manuscript of 1 March 2004.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {R : Type*} [Group R] [Finite R]

theorem cocycle_of_elementary_kernel_quotient (N : Subgroup R) [N.Normal]
    [IsElementaryAbelian 2 N] [IsElementaryAbelian 2 (R ⧸ N)]
    (α : R →* R) (hα : ∀ x, α (α x) = x) (hN : ∀ x ∈ N, α x ∈ N)
    (hcN : Nat.card ((α.restrict hN).eqLocus (MonoidHom.id N)) ^ 2 = Nat.card N)
    (hcQ : Nat.card ((QuotientGroup.map N N α hN).eqLocus
      (MonoidHom.id (R ⧸ N))) ^ 2 = Nat.card (R ⧸ N))
    (x : R) (hx : x * α x = 1) : ∃ y : R, x = y * α y⁻¹ := by
  apply cocycle_of_elementary_quotient (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) α hα (QuotientGroup.map N N α hN) _
    (fun _ => rfl) hcQ _ x hx
  · intro a
    obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective N a
    change QuotientGroup.mk' N (α (α r)) = QuotientGroup.mk' N r
    rw [hα]
  · intro r hr hr2
    have hrN : r ∈ N := (QuotientGroup.eq_one_iff r).mp hr
    have hinv (a : N) : a⁻¹ = a := by
      apply inv_eq_of_mul_eq_one_left
      simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 N) a
    have hfix : (α.restrict hN) ⟨r,hrN⟩ = ⟨r,hrN⟩ := by
      apply Subtype.ext
      exact (eq_inv_of_mul_eq_one_right hr2).trans (congrArg (fun a : N => a.val) (hinv ⟨r,hrN⟩))
    have hαN : ∀ a : N, (α.restrict hN) ((α.restrict hN) a) = a := by
      intro a
      exact Subtype.ext (hα a.val)
    obtain ⟨y,hy⟩ := elementary_fixed_is_coboundary (A := N) (α.restrict hN)
      hαN hcN ⟨r,hrN⟩ hfix
    exact ⟨y.val,congrArg (fun a : N => a.val) hy⟩

variable {G : Type*} [Group G] [Finite G]

theorem involution_coset_fusion_of_elementary_layers
    (R : Subgroup G) (N : Subgroup R) [N.Normal]
    [IsElementaryAbelian 2 N] [IsElementaryAbelian 2 (R ⧸ N)]
    (s : G) (hs : s ^ 2 = 1) (hsR : s ∈ normalizer (R : Set G))
    (hN : ∀ x ∈ N, R.normalizerMonoidHom ⟨s,hsR⟩ x ∈ N)
    (hcN : Nat.card (((R.normalizerMonoidHom ⟨s,hsR⟩).toMonoidHom.restrict hN).eqLocus
      (MonoidHom.id N)) ^ 2 = Nat.card N)
    (hcQ : Nat.card ((QuotientGroup.map N N
      (R.normalizerMonoidHom ⟨s,hsR⟩).toMonoidHom hN).eqLocus
      (MonoidHom.id (R ⧸ N))) ^ 2 = Nat.card (R ⧸ N))
    (v : G) (hv : v ^ 2 = 1) (hcoset : v * s⁻¹ ∈ R) :
    ∃ r ∈ R, r * s * r⁻¹ = v := by
  let α := (R.normalizerMonoidHom ⟨s,hsR⟩).toMonoidHom
  have hs' : s*s=1 := by simpa only [pow_two] using hs
  have hα : ∀ x, α (α x) = x := by
    intro x
    apply Subtype.ext
    change s * (s * x.val * s⁻¹) * s⁻¹ = x.val
    calc
      _ = (s*s) * x.val * (s*s)⁻¹ := by group
      _ = x.val := by rw [hs']; simp
  let x : R := ⟨v*s⁻¹,hcoset⟩
  have hx : x * α x = 1 := by
    apply Subtype.ext
    change (v*s⁻¹) * (s * (v*s⁻¹) * s⁻¹) = 1
    have hv' : v*v=1 := by simpa only [pow_two] using hv
    calc
      _ = (v*v) * (s*s)⁻¹ := by group
      _ = 1 := by rw [hv',hs']; simp
  obtain ⟨r,hr⟩ := cocycle_of_elementary_kernel_quotient N α hα hN hcN hcQ x hx
  refine ⟨r,r.property,?_⟩
  have he := congrArg (fun a : R => a.val) hr
  change v*s⁻¹ = r.val * (s * r.val⁻¹ * s⁻¹) at he
  have hh := congrArg (fun a : G => a*s) he
  simpa only [inv_mul_cancel_right, mul_assoc, inv_mul_cancel, mul_one] using hh.symm
end Theory.GroupTheory
