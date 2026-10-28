module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ResidualFactors
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.CenterProduct
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.SwappedTrace
public import Theory.GroupTheory.CentralPResidualCommutator

/-!
# Centers and the odd trace in the binary block argument

The global He bridge applies to XT. Normal-subgroup inheritance gives
characteristic two in X, so Z(X) is a two-group. Two-perfectness then kills
central commutator maps into Z(X), proving Z(X/Z(X)) = 1. Thus applying
A.1.15 to this quotient will introduce no additional central factor.

The residual W = O²(X ∩ K) is normal in X. Modulo W, the image of Z(X)
is a two-group, and hence has trivial intersection with the image of P.
All odd-order elements of P ∩ K lie in W. These facts prove the actual
trace P ∩ WZ(X) = P ∩ K without additional model assumptions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
1.3.8, printed p.514, with the global 1.1.4(6) He implication explicit.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter1.RadicalExclusions
open XiEmbedding
variable {G : Type*} [Group G] [Finite G]

/-- Characteristic two passes from XT to its normal subgroup X. -/
theorem xi_core_selfCentralizing_of_global_He {T X : Subgroup G}
    (h114 : HOver G (T : Set G) ⊆ He G) (hX : X ∈ Xi G T) :
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X := by
  have hH : X ⊔ T ∈ HOver G (T : Set G) := ⟨hX.join_mem_H, fun _ ht => mem_sup_right ht⟩
  have hn : (X.subgroupOf (X ⊔ T)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hX.invariant)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe (show X ≤ X ⊔ T from le_sup_left))).mp
      (subnormal_core_selfCentralizing (mem_He_iff.mp (h114 hH)) _ hn.isSubnormal)

/-- The center of the actual subgroup X is a two-group. -/
theorem xi_center_isPGroup_of_global_He {T X : Subgroup G}
    (h114 : HOver G (T : Set G) ⊆ He G) (hX : X ∈ Xi G T) :
    IsPGroup 2 (center X) := by
  have hz : center X ≤ pCore 2 X :=
    (center_le_centralizer _).trans (xi_core_selfCentralizing_of_global_He h114 hX)
  exact pCore_isPGroup.of_injective (inclusion hz) (inclusion_injective hz)

/-- No extra center appears after taking the central quotient. -/
theorem xi_center_quotient_center_eq_bot {T X : Subgroup G}
    (h114 : HOver G (T : Set G) ⊆ He G) (hX : X ∈ Xi G T) :
    center (X ⧸ center X) = ⊥ := by
  apply bot_unique
  intro a ha
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (center X) a
  have hb : ∀ x : X, ⁅(x : G), (b : G)⁆ ∈ (center X).map X.subtype := by
    intro x
    have hcomm : ⁅x, b⁆ ∈ center X := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (center X) ⁅x, b⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp ha _)
    exact mem_map.mpr ⟨⁅x, b⁆, hcomm, rfl⟩
  have hc := commute_of_central_p_commutator_of_isPPerfect X (center X)
    hX.perfect (xi_center_isPGroup_of_global_He h114 hX) le_rfl (b : G) hb
  apply (QuotientGroup.eq_one_iff b).mpr
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (hc x x.property).symm.eq

private theorem odd_inf_sup_center {D : Type*} [Group D]
    {p : ℕ} {P W : Subgroup D} [W.Normal]
    (hp : Odd p) (hP : IsPGroup p P) (hZ : IsPGroup 2 (center D)) :
    P ⊓ (W ⊔ center D) = P ⊓ W := by
  apply le_antisymm ?_ (inf_le_inf_left _ le_sup_left)
  intro a ha
  let q := QuotientGroup.mk' W
  have hqaP : q a ∈ P.map q := mem_map.mpr ⟨a, ha.1, rfl⟩
  have hqaZ : q a ∈ (center D).map q := by
    have hm : q a ∈ (W ⊔ center D).map q := mem_map.mpr ⟨a, ha.2, rfl⟩
    simpa only [Subgroup.map_sup, q, QuotientGroup.map_mk'_self, bot_sup_eq] using hm
  have he : q a = 1 := disjoint_def.mp
    ((hP.map q).disjoint_of_coprime (hZ.map q) hp.coprime_two_right) hqaP hqaZ
  exact ⟨ha.1, (QuotientGroup.eq_one_iff a).mp he⟩

/-- The center-enlarged residual factor has exactly the trace P ∩ K. -/
theorem BinaryBlockEmbedding.odd_trace {p : ℕ} {T X P L₀ M H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K) (hc : Configuration p T X P L₀ M)
    (h114 : HOver G (T : Set G) ⊆ He G) :
    P ⊓ (blockResidual X K ⊔ (center X).map X.subtype) = P ⊓ K := by
  let _ : Fact p.Prime := ⟨hc.prime⟩
  let W := blockResidual X K
  have hWX : W ≤ X := (blockResidual_le X K).trans inf_le_left
  have hPX : P ≤ X := h.local_input.complement_le
  have hXK : X ≤ normalizer K := h.containment.trans
    (cComponentOrbit_le_normalizer h.component (le_sup_right.trans h.local_input.overgroup))
  let _ : (W.subgroupOf X).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizes_blockResidual X.le_normalizer hXK)
  have he := odd_inf_sup_center (P := P.subgroupOf X) (W := W.subgroupOf X) hc.odd
    (h.local_input.odd_complement.isPGroup.comap_subtype (K := X))
    (xi_center_isPGroup_of_global_He h114 hc.xi)
  have hemap := congrArg (map X.subtype) he
  rw [map_inf _ _ _ X.subtype_injective, Subgroup.map_sup,
    map_subgroupOf_eq_of_le hPX, map_subgroupOf_eq_of_le hWX,
    map_inf _ _ _ X.subtype_injective, map_subgroupOf_eq_of_le hPX,
    map_subgroupOf_eq_of_le hWX] at hemap
  refine hemap.trans (le_antisymm (inf_le_inf_left P ((blockResidual_le X K).trans inf_le_right)) ?_)
  intro a ha
  refine ⟨ha.1, mem_map.mpr ⟨⟨a, hPX ha.1, ha.2⟩, ?_, rfl⟩⟩
  apply mem_pResidual_of_orderOf_coprime
  have ho := (h.local_input.odd_complement.isPGroup.orderOf_coprime
    hc.odd.coprime_two_right ⟨a, ha.1⟩).symm
  change Nat.Coprime 2 (orderOf (⟨a, hPX ha.1, ha.2⟩ : (X ⊓ K : Subgroup G)))
  rw [← Subgroup.orderOf_coe (⟨a, hPX ha.1, ha.2⟩ : (X ⊓ K : Subgroup G))]
  simpa only [← Subgroup.orderOf_coe] using ho

end CFSG.Quasithin.Chapter1.RadicalExclusions
