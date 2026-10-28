module

public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PGroup.MutualNormalizerCommutator


/-!
# Inversion modulo the two-core and a normal subgroup

Suppose X is two-perfect and mutually normalizes a two-subgroup S.
If t inverts X/O₂(X), and t agrees modulo a normal subgroup C with
an element of S, then X lies in C. Mutual normalization puts [X,S]
in O₂(X); consequently every square in the image of X modulo C lies
in the image of O₂(X). That image of X is a two-group, hence trivial.

Source application: Aschbacher–Smith, proof of 13.8.20, printed p.954,
correcting the prescribed inverter by an inner Sylow element.
-/

public section

open Subgroup
open scoped commutatorElement

namespace Subgroup
variable {G : Type*} [Group G]

/-- A two-perfect subgroup inverted modulo its two-core lies in C when the
inverter agrees modulo C with a mutually normalizing two-element. -/
theorem le_normal_of_inversion_mod_twoCore (X S C : Subgroup G) [C.Normal]
    (hX : IsPPerfect 2 X) (hS : IsPGroup 2 S)
    (hXS : X ≤ normalizer (S : Set G)) (hSX : S ≤ normalizer (X : Set G))
    (t s : G) (hs : s ∈ S) (hc : s⁻¹ * t ∈ C)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ * x ∈ X.pCoreIn 2) : X ≤ C := by
  let f := QuotientGroup.mk' C
  have hts : f t = f s := by
    have he := (QuotientGroup.eq_one_iff (s⁻¹ * t)).mpr hc
    change f (s⁻¹ * t) = 1 at he
    exact (inv_mul_eq_one.mp (by simpa only [map_mul, map_inv] using he)).symm
  have hcomm := commutator_le_pCore_of_mutual_normalization X S hS hXS hSX
  have hsq (x : G) (hx : x ∈ X) : (f x) ^ 2 ∈ (X.pCoreIn 2).map f := by
    have hi := mem_map_of_mem f (hinv x hx)
    have hd : s * x * s⁻¹ * x⁻¹ ∈ X.pCoreIn 2 := by
      apply hcomm
      rw [commutator_comm]
      exact commutator_mem_commutator hs hx
    have hm := ((X.pCoreIn 2).map f).mul_mem
      (((X.pCoreIn 2).map f).inv_mem (mem_map_of_mem f hd)) hi
    simp only [map_mul, map_inv, hts] at hm
    convert hm using 1
    simp only [pow_two]
    group
  have hp : IsPGroup 2 (X.map f) := by
    rintro ⟨y, x, hx, rfl⟩
    obtain ⟨n, hn⟩ := ((isPGroup_pCoreIn 2 X).map f).exists_pow_pow_eq_one
      ⟨(f x) ^ 2, hsq x hx⟩
    refine ⟨n + 1, Subtype.ext ?_⟩
    have hh := congrArg Subtype.val hn
    change (f x) ^ (2 ^ (n + 1)) = 1
    simpa only [Subgroup.coe_pow, Subtype.coe_mk, Subgroup.coe_one,
      ← pow_mul, ← Nat.pow_succ'] using hh
  have he := hX.hom_eq_one_of_isPGroup hp (f.subgroupMap X)
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  exact congrArg (fun z : X →* X.map f => (z ⟨x, hx⟩ : G ⧸ C)) he

end Subgroup
