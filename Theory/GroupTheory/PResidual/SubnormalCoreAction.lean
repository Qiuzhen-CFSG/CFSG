module

public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.PGroup.Subnormal
public import Theory.GroupTheory.CentralPChiefCore

/-!+# Normal p-subgroups acting on subnormal p-perfect subgroups

If B is subnormal and p-perfect, every p-subgroup Q normalized by B also
normalizes B. Indeed B is the p-residual of BQ, by the subnormal supplement
theorem. Consequently [Q,B] lies in O_p(B). Coprime commutator idempotence
improves this to [Q,B] ≤ [O_p(B),B] in a finite group.

This supplies the relative-subnormal step needed when testing short groups
against local radicals. No assertion that B equals a local group is used.
Source: Aschbacher–Smith, A.4.2(2), printed p.57, and the commutator
argument of C.6.3, printed pp.166–167.
-/

public section

namespace Subgroup

open scoped Pointwise

variable {G : Type*} [Group G] {p : ℕ}

/-- A p-subgroup normalized by a subnormal p-perfect subgroup normalizes it
in return. Neither subgroup is assumed normal in the ambient group. -/
theorem le_normalizer_of_isSubnormal_isPPerfect (B Q : Subgroup G)
    (hB : B.IsSubnormal) (hpB : IsPPerfect p B) (hpQ : IsPGroup p Q)
    (hBQ : B ≤ normalizer Q) : Q ≤ normalizer B := by
  let K := B ⊔ Q
  have hBK : B ≤ K := le_sup_left
  have hQK : Q ≤ K := le_sup_right
  have hprod : ∀ k : K, ∃ b ∈ B.subgroupOf K, ∃ q ∈ Q.subgroupOf K, b * q = k := by
    intro k
    have hk : (k : G) ∈ (B : Set G) * (Q : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right B Q hBQ]
      exact k.property
    obtain ⟨b, hb, q, hq, he⟩ := hk
    exact ⟨⟨b, hBK hb⟩, hb, ⟨q, hQK hq⟩, hq, Subtype.ext he⟩
  have hpBK : IsPPerfect p (B.subgroupOf K) :=
    hpB.of_surjective (subgroupOfEquivOfLe hBK).symm.toMonoidHom
      (subgroupOfEquivOfLe hBK).symm.surjective
  have he := pResidual_eq_of_subnormal_product (B.subgroupOf K) (Q.subgroupOf K)
    hB.subgroupOf hpBK hpQ.comap_subtype hprod
  have hn : (B.subgroupOf K).Normal := he ▸ inferInstance
  exact hQK.trans ((normal_subgroupOf_iff_le_normalizer hBK).mp hn)

/-- A finite p-perfect group acts idempotently on a p-subgroup it normalizes. -/
theorem commutator_isPPerfect_idempotent [Finite G] [Fact p.Prime]
    (B Q : Subgroup G) (hpB : IsPPerfect p B) (hpQ : IsPGroup p Q)
    (hBQ : B ≤ normalizer Q) : ⁅⁅Q, B⁆, B⁆ = ⁅Q, B⁆ := by
  have hgen := closure_coprime_order_eq_top_of_pResidual_eq_top p
    ((pResidual_eq_top_iff p B).mpr hpB)
  have hh := commutator_coprime_order_generators_idempotent p Q B hpQ hBQ
  simpa only [hgen, ← MonoidHom.range_eq_map, range_subtype] using hh

/-- The external radical commutator lies in the intrinsic core commutator
layer of the subnormal p-perfect subgroup. -/
theorem commutator_le_core_commutator_of_isSubnormal [Finite G] [Fact p.Prime]
    (B Q : Subgroup G) (hB : B.IsSubnormal)
    (hpB : IsPPerfect p B) (hpQ : IsPGroup p Q)
    (hBQ : B ≤ normalizer Q) :
    ⁅Q, B⁆ ≤ (⁅pCore p B, (⊤ : Subgroup B)⁆).map B.subtype := by
  have hQB := le_normalizer_of_isSubnormal_isPPerfect B Q hB hpB hpQ hBQ
  have hcB : ⁅Q, B⁆ ≤ B := le_normalizer_iff_commutator_le_right.mp hQB
  have hcQ : ⁅Q, B⁆ ≤ Q := le_normalizer_iff_commutator_le_left.mp hBQ
  have hn : (⁅Q, B⁆.subgroupOf B).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right Q B)
  have hcore : ⁅Q, B⁆ ≤ (pCore p B).map B.subtype :=
    isPGroup_le_pCoreAmbient_of_isSubnormalIn B ⁅Q, B⁆ p hcB hn.isSubnormal
      (hpQ.to_le hcQ)
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  exact (commutator_isPPerfect_idempotent B Q hpB hpQ hBQ).symm.le.trans
    (commutator_mono hcore le_rfl)

end Subgroup

end
