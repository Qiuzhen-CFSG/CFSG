module
public import Theory.GroupAction.ElementaryTwoInvertedPrimePower
public import Mathlib.Tactic.Group
/-!
# Actual two-conjugate pairs from inverted odd-prime-power elements

An odd-order element inverted by a member of V belongs to ⟨V,V^g⟩:
the pair contains its square, which generates the same cyclic subgroup.
Consequently this pair is exactly ⟨g⟩V when every element of V fixes or
inverts g. The coprime hyperplane theorem produces such a nontrivial g
inside the prescribed odd-prime group.
Source: Aschbacher–Smith E.2.7, solvable branch, printed p.218.
-/
public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem conjugate_join_eq_cyclic_sup (V : Subgroup G) (g v : G)
    (hv : v ∈ V) (ho : Odd (orderOf g)) (hinv : v*g*v⁻¹ = g⁻¹) :
    V ⊔ V.map (MulAut.conj g).toMonoidHom = zpowers g ⊔ V := by
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  have hvI : v ∈ I := mem_sup_left hv
  have hconj : g*v*g⁻¹ ∈ I := mem_sup_right (mem_map_of_mem (MulAut.conj g).toMonoidHom hv)
  have hsq : g^2 ∈ I := by
    have hconjinv : v*g⁻¹*v⁻¹ = g := by
      have hh := congrArg Inv.inv hinv
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using hh
    have he : (g*v*g⁻¹)*v⁻¹ = g^2 := by
      rw [mul_assoc g v, mul_assoc g, hconjinv, pow_two]
    exact he ▸ I.mul_mem hconj (I.inv_mem hvI)
  have hgI : g ∈ I :=
    (zpowers_le.mpr hsq) (mem_zpowers_pow_iff.mpr (Nat.coprime_two_left.mpr ho))
  refine le_antisymm ?_ (sup_le (zpowers_le.mpr hgI) le_sup_left)
  refine sup_le le_sup_right ?_
  rintro x ⟨w,hw,rfl⟩
  exact (zpowers g ⊔ V).mul_mem
    ((zpowers g ⊔ V).mul_mem (mem_sup_left (mem_zpowers g)) (mem_sup_right hw))
    ((zpowers g ⊔ V).inv_mem (mem_sup_left (mem_zpowers g)))

theorem normalizes_cyclic_of_identity_or_inversion (V : Subgroup G) (g : G)
    (hsign : ∀ v ∈ V, v*g*v⁻¹ = g ∨ v*g*v⁻¹ = g⁻¹) :
    V ≤ normalizer (zpowers g : Set G) := by
  intro v hv
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change zpowers (v*g*v⁻¹) = zpowers g
  rcases hsign v hv with h | h
  · rw [h]
  · rw [h, zpowers_inv]

/-- The original moved elementary actor supplies a pair with an internal
odd-prime-power conjugator and the stated cyclic normal factor. -/
theorem exists_prime_power_conjugate_pair [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (R V : Subgroup G) (hR : IsPGroup p R)
    [IsElementaryAbelian 2 V] (hVR : V ≤ normalizer (R : Set G))
    (hne : ⁅R,V⁆ ≠ ⊥) :
    ∃ (g : G) (a : ℕ), g ∈ R ∧ 0 < a ∧ orderOf g = p ^ a ∧
      g ∈ V ⊔ V.map (MulAut.conj g).toMonoidHom ∧
      V ⊔ V.map (MulAut.conj g).toMonoidHom = zpowers g ⊔ V ∧
      V ≤ normalizer (zpowers g : Set G) := by
  obtain ⟨g,v,a,hg,hv,ha,ho,hinv,hsign⟩ :=
    Theory.GroupAction.exists_inverted_prime_power_line hp R V hR hVR hne
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  have he := conjugate_join_eq_cyclic_sup V g v hv (ho.symm ▸ hpodd.pow) hinv
  exact ⟨g,a,hg,ha,ho,he.symm ▸ mem_sup_left (mem_zpowers g),he,
    normalizes_cyclic_of_identity_or_inversion V g hsign⟩
end Theory.GroupTheory
