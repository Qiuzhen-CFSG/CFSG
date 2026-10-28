module

public import Theory.GroupTheory.SylowCentralizerComplement
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Centralizer comparison from a Sylow-fixed point

In a group of characteristic two, a Sylow-central element lies in the two-core.
If the Sylow normalizes a two-perfect subgroup K, two-perfect commutator
idempotence puts its displacement by K in [O₂(K),K]. When this layer is
contained in an elementary K-module U, averaging over an intrinsic Sylow
subgroup gives a K-fixed representative modulo U. Equality of the D- and
K-fixed subgroups of U then turns D-fixation of the original point into
K-fixation.

This is the centralizing consequence of the B.2.14 supplement in
Aschbacher–Smith, Lemma 13.6.22, printed p.933. The proof constructs the
fixed representative using Sylow averaging, without a supplied supplement.
-/

public section
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Mutual normalization places an external two-group commutator in the
intrinsic core commutator of a two-perfect subgroup. -/
theorem commutator_le_core_commutator_of_mutual_normalization (K Q : Subgroup G)
    (hK : IsPPerfect 2 K) (hQ : IsPGroup 2 Q)
    (hKQ : K ≤ normalizer (Q : Set G)) (hQK : Q ≤ normalizer (K : Set G)) :
    ⁅Q, K⁆ ≤ (⁅pCore 2 K, (⊤ : Subgroup K)⁆).map K.subtype := by
  have hCK : ⁅Q, K⁆ ≤ K := le_normalizer_iff_commutator_le_right.mp hQK
  have hCQ : ⁅Q, K⁆ ≤ Q := le_normalizer_iff_commutator_le_left.mp hKQ
  have hnormal : (⁅Q, K⁆.subgroupOf K).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right _ _)
  have hcore := isPGroup_le_pCoreAmbient_of_isSubnormalIn K ⁅Q, K⁆ 2 hCK
    hnormal.isSubnormal (hQ.to_le hCQ)
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  exact (commutator_isPPerfect_idempotent K Q hK hQ hKQ).symm.le.trans
    (commutator_mono hcore le_rfl)

/-- A Sylow-fixed point centralizing D centralizes K when the elementary core
commutator has the same D- and K-fixed subgroups. Sylow averaging constructs
the centralizing representative; no complement or splitting is assumed. -/
theorem mem_centralizer_of_sylow_fixed_core_comparison (S : Sylow 2 G) (K D U : Subgroup G)
    [IsElementaryAbelian 2 U]
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hK : IsPPerfect 2 K) (hn : (S : Subgroup G) ≤ normalizer (K : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hcore : (⁅pCore 2 K, (⊤ : Subgroup K)⁆).map K.subtype ≤ U)
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype ≤ S)
    (hDK : D ≤ K)
    (hfix : U ⊓ centralizer (D : Set G) = U ⊓ centralizer (K : Set G))
    (a : G) (ha : a ∈ centralizer (S : Set G))
    (haD : a ∈ centralizer (D : Set G)) :
    a ∈ centralizer (K : Set G) := by
  have haQ : a ∈ pCore 2 G := hchar
    (centralizer_le (pCore_isPGroup.le_sylow_of_normal S) ha)
  have hc := (commutator_le_core_commutator_of_mutual_normalization K (pCore 2 G)
    hK pCore_isPGroup le_normalizer_of_normal
    ((pCore_isPGroup.le_sylow_of_normal S).trans hn)).trans hcore
  obtain ⟨u, hu, huc⟩ := fixed_coset_of_sylow K U hKU
    (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu) P a
    (fun k hk => by
      apply hc
      rw [commutator_comm]
      exact commutator_mem_commutator hk haQ)
    (fun k hk => ha k (hP (mem_map_of_mem K.subtype hk)))
  have huD : u ∈ centralizer (D : Set G) := by
    have hh := (centralizer (D : Set G)).mul_mem (centralizer_le hDK huc)
      ((centralizer (D : Set G)).inv_mem haD)
    simpa only [mul_inv_cancel_right] using hh
  have huK := (hfix.le ⟨hu, huD⟩).2
  have hh := (centralizer (K : Set G)).mul_mem
    ((centralizer (K : Set G)).inv_mem huK) huc
  simpa only [inv_mul_cancel_left] using hh

end Subgroup
