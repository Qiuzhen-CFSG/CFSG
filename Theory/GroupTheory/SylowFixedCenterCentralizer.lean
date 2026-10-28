module
public import Theory.GroupTheory.SylowFixedCoreCentralizer

/-!
# Sylow-fixed centralizer comparison using the center of the two-core

A Sylow-central element in characteristic two lies in O₂(G) and centralizes
O₂(K). The subgroup Q = O₂(G) ∩ C_G(O₂(K)) is normalized by K and normalizes
K. Hence [Q,K] lies in Z(O₂(K)); two-perfection improves this to
[Q,K] ≤ [Z(O₂(K)),K]. Averaging in an elementary layer containing this
center commutator gives the same centralizer comparison as for short groups,
without requiring the full core commutator to be abelian.

Source: Aschbacher–Smith, 13.6.22, printed p.933, using B.2.14.
-/

public section
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem commutator_le_core_center_commutator_of_mutual_normalization
    (K Q : Subgroup G) (hK : IsPPerfect 2 K) (hQ : IsPGroup 2 Q)
    (hKQ : K ≤ normalizer (Q : Set G)) (hQK : Q ≤ normalizer (K : Set G))
    (hc : Q ≤ centralizer ((pCore 2 K).map K.subtype : Set G)) :
    ⁅Q, K⁆ ≤ ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆ := by
  have hCK : ⁅Q, K⁆ ≤ K := le_normalizer_iff_commutator_le_right.mp hQK
  have hCQ : ⁅Q, K⁆ ≤ Q := le_normalizer_iff_commutator_le_left.mp hKQ
  have hnormal : (⁅Q, K⁆.subgroupOf K).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right _ _)
  have hcore := isPGroup_le_pCoreAmbient_of_isSubnormalIn K ⁅Q, K⁆ 2 hCK
    hnormal.isSubnormal (hQ.to_le hCQ)
  have hz : ⁅Q, K⁆ ≤ ((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype := by
    intro x hx
    obtain ⟨k, hk, he⟩ := hcore hx
    refine ⟨k, ⟨⟨k, hk⟩, mem_center_iff.mpr ?_, rfl⟩, he⟩
    intro y
    apply Subtype.ext
    apply Subtype.ext
    change (y.val : G) * (k : G) = (k : G) * (y.val : G)
    change (k : G) = x at he
    rw [he]
    exact hc (hCQ hx) (y.val : G) (mem_map_of_mem K.subtype y.property)
  exact (commutator_isPPerfect_idempotent K Q hK hQ hKQ).symm.le.trans
    (commutator_mono hz le_rfl)

/-- A Sylow-fixed point is controlled by the center commutator, even when
its two-core is nonabelian. -/
theorem mem_centralizer_of_sylow_fixed_center_comparison
    (S : Sylow 2 G) (K D U : Subgroup G) [IsElementaryAbelian 2 U]
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hK : IsPPerfect 2 K) (hn : (S : Subgroup G) ≤ normalizer (K : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hcore : ⁅((center (pCore 2 K)).map (pCore 2 K).subtype).map K.subtype, K⁆ ≤ U)
    (P : Sylow 2 K) (hP : (P : Subgroup K).map K.subtype ≤ S)
    (hDK : D ≤ K)
    (hfix : U ⊓ centralizer (D : Set G) = U ⊓ centralizer (K : Set G))
    (a : G) (ha : a ∈ centralizer (S : Set G))
    (haD : a ∈ centralizer (D : Set G)) :
    a ∈ centralizer (K : Set G) := by
  let R := (pCore 2 K).map K.subtype
  let Q := pCore 2 G ⊓ centralizer (R : Set G)
  have hRS : R ≤ S := (map_mono (pCore_isPGroup.le_sylow_of_normal P)).trans hP
  have haQ : a ∈ Q := ⟨hchar
    (centralizer_le (pCore_isPGroup.le_sylow_of_normal S) ha), centralizer_le hRS ha⟩
  have hKR : K ≤ normalizer (R : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 K).le_normalizer_map K.subtype
  have hRC : normalizer (R : Set G) ≤ normalizer (centralizer (R : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (R : Set G))).mp
      (normal_subgroupOf_centralizer_normalizer (R : Set G))
  have hKQ : K ≤ normalizer (Q : Set G) :=
    (le_inf le_normalizer_of_normal
      (hKR.trans hRC)).trans inf_normalizer_le_normalizer_inf
  have hc := (commutator_le_core_center_commutator_of_mutual_normalization K Q hK
    (pCore_isPGroup.to_le inf_le_left) hKQ
    (inf_le_left.trans ((pCore_isPGroup.le_sylow_of_normal S).trans hn)) inf_le_right).trans hcore
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
