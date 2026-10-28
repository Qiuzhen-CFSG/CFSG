module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A self-centralizing normal p-subgroup forces characteristic p

If Q ≤ M normalizes inside M and C_G(Q) ≤ Q, then C_M(O_p(M)) ≤ O_p(M).
Indeed Q, viewed as a subgroup of M, is normal and lies in O_p(M). Any
element centralizing O_p(M) therefore centralizes Q and belongs to Q.

This local criterion is used for the rank-one examples in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Theorem 0.1.2, printed p.4.
Normality is relative to M; no ambient normality of Q is required.
-/

open Subgroup

public theorem centralizer_pCore_le_of_normalized {G : Type*} [Group G]
    (p : ℕ) (Q M : Subgroup G) (hp : IsPGroup p Q)
    (hQM : Q ≤ M) (hMN : M ≤ normalizer (Q : Set G))
    (hc : centralizer (Q : Set G) ≤ Q) :
    centralizer (pCore p M : Set M) ≤ pCore p M := by
  have hn : (Q.subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQM).mpr hMN
  have hQcore : Q.subgroupOf M ≤ pCore p M :=
    le_sSup ⟨hn, hp.comap_subtype⟩
  intro x hx
  apply hQcore
  change (x : G) ∈ Q
  apply hc
  rw [mem_centralizer_iff] at hx ⊢
  intro y hy
  exact congrArg Subtype.val (hx ⟨y, hQM hy⟩ (hQcore hy))
