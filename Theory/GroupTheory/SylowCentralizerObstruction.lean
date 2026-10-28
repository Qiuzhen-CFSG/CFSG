module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A Sylow centralizer obstruction

If an ambient Sylow p-subgroup centralizes U, every p-subgroup normalizing U
also centralizes U. Indeed C_G(U) is normal in N_G(U), contains a Sylow
p-subgroup there, and therefore contains all of its p-subgroups.

This supplies the final contradiction in Aschbacher–Smith, Theorem 16.3.7,
printed p.1182: the invariant four-group Ω₁(Φ(J(P))) cannot both be
centralized by an ambient Sylow two-subgroup and acted on nontrivially by P.
The Thompson-subgroup computations establishing those premises are separate.
-/

open Subgroup
open scoped Pointwise

private theorem pSubgroup_le_normal_of_sylow_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (N Q : Subgroup G) [N.Normal]
    (hTN : (T : Subgroup G) ≤ N) (hQ : IsPGroup p Q) : Q ≤ N := by
  obtain ⟨R, hQR⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R T
  intro q hq
  have hc : g * q * g⁻¹ ∈ N := by
    apply hTN
    rw [← hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hQR hq)
  have hi := (inferInstance : N.Normal).conj_mem (g * q * g⁻¹) hc g⁻¹
  simpa [mul_assoc] using hi

/-- Any p-subgroup normalizing a subgroup centralized by an ambient Sylow
p-subgroup centralizes it. The proof uses normality of the centralizer inside
the normalizer and Sylow conjugacy there. -/
public theorem Sylow.normalizing_pSubgroup_le_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (U Q : Subgroup G)
    (hTU : (T : Subgroup G) ≤ centralizer (U : Set G))
    (hQ : IsPGroup p Q) (hQU : Q ≤ normalizer (U : Set G)) :
    Q ≤ centralizer (U : Set G) := by
  let N := normalizer (U : Set G)
  let C := (centralizer (U : Set G)).subgroupOf N
  have hTN : (T : Subgroup G) ≤ N := hTU.trans (centralizer_le_normalizer _)
  have hc := pSubgroup_le_normal_of_sylow_le (T.subtype hTN) C (Q.subgroupOf N)
    (show ((T.subtype hTN : Sylow p N) : Subgroup N) ≤ C from fun x hx => hTU hx)
    (hQ.comap_of_injective N.subtype N.subtype_injective)
  intro q hq
  exact hc (show (⟨q, hQU hq⟩ : N) ∈ Q.subgroupOf N from hq)

/-- A p-subgroup acting nontrivially on an invariant subgroup cannot have
that subgroup centralized by an ambient Sylow p-subgroup. -/
public theorem Sylow.not_centralizes_of_normalized_noncentral
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (U Q : Subgroup G)
    (hQ : IsPGroup p Q) (hQU : Q ≤ normalizer (U : Set G))
    (hnoncentral : ¬ Q ≤ centralizer (U : Set G)) :
    ¬ (T : Subgroup G) ≤ centralizer (U : Set G) := by
  intro hTU
  exact hnoncentral (T.normalizing_pSubgroup_le_centralizer U Q hTU hQ hQU)
