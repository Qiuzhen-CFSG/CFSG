module
public import Theory.GroupTheory.SylowElementConjugacy
public import Mathlib.GroupTheory.Subgroup.Centralizer
/-!
# Nonfusion from a unique involution square

If every element of order four in a Sylow subgroup of C_G(j) squares to z,
with j distinct from z, then j cannot be conjugate to the square of any
order-four element of G. Conjugate a proposed root into C_G(j), then into
its chosen Sylow subgroup; the second conjugator fixes j.

This replaces full Sylow-centralizer identification in the separating
involution argument of Aschbacher–Smith 14.2.17(1), printed p.987.
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

public theorem not_isConj_square_of_unique_square
    (j z : G) (P : Sylow 2 (centralizer ({j} : Set G)))
    (hsquare : ∀ x : P, orderOf x = 4 → ((x : centralizer ({j} : Set G)) : G)^2 = z)
    (hjz : j ≠ z) (r : G) (hr : orderOf r = 4) : ¬ IsConj (r^2) j := by
  intro h
  obtain ⟨a,ha⟩ := isConj_iff.mp h
  let s := MulAut.conj a r
  have hs2 : s^2=j := (map_pow (MulAut.conj a) r 2).symm.trans ha
  have hs : orderOf s=4 := ((MulAut.conj a).orderOf_eq r).trans hr
  have hsj : Commute s j := by rw [←hs2]; exact Commute.self_pow s 2
  let sc : centralizer ({j} : Set G) := ⟨s,mem_centralizer_singleton_iff.mpr hsj.eq⟩
  have hsc : orderOf sc=2^2 := (orderOf_coe sc).symm.trans hs
  obtain ⟨t,ht⟩ := P.exists_isConj_of_orderOf_eq_prime_pow hsc
  obtain ⟨b,hb⟩ := isConj_iff.mp ht
  have ht4 : orderOf t=4 := by
    rw [←orderOf_coe,←hb]
    exact ((MulAut.conj b).orderOf_eq sc).trans hsc
  have hbs : ((t:centralizer ({j}:Set G)):G)^2=j := by
    have he := congrArg (fun x : centralizer ({j}:Set G) => (x:G)) hb
    change (b:G)*s*(b:G)⁻¹=((t:centralizer ({j}:Set G)):G) at he
    rw [←he]
    change (MulAut.conj (b:G) s)^2=j
    rw [←map_pow,hs2]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp b.property)
  exact hjz (hbs.symm.trans (hsquare t ht4))
end Subgroup
