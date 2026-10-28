module
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
public import Mathlib.Tactic

/-!
# A large commutator kernel from a four-element quotient action

Suppose B normalizes subgroups U and R, with R normal in U and |U:R|=4.
If B fixes an element of U outside R, then B has a subgroup of index at
most two whose commutator with U lies in R. No commutativity or exponent
hypothesis on U is needed.

Use the literal conjugation action on U/R. Its automorphism range fixes
the nonidentity image of the given element, so the four-element automorphism
stabilizer bound gives range order at most two. Include the action kernel
back into the ambient group, preserving its cardinality, and translate
trivial quotient action to the exact commutator containment.

This is the elementary action argument used with the selected natural
support in Stellmacher (9.9), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`; the theorem is source-neutral.
-/

open scoped commutatorElement
namespace Subgroup
universe u

public theorem exists_large_subgroup_commutator_le_of_quotient_four
    {G : Type u} [Group G] [Finite G]
    (B U R : Subgroup G) (hRU : R ≤ U)
    (hBU : B ≤ normalizer (U : Set G))
    (hBR : B ≤ normalizer (R : Set G))
    (hN : (R.subgroupOf U).Normal)
    (hcard : Nat.card U = 4 * Nat.card R)
    (fixed : G) (hfixedU : fixed ∈ U) (hfixedR : fixed ∉ R)
    (hfix : B ≤ centralizer ({fixed} : Set G)) :
    ∃ C : Subgroup G, C ≤ B ∧ Nat.card B ≤ 2 * Nat.card C ∧ ⁅U, C⁆ ≤ R := by
  classical
  let _ := hN
  let W := U ⧸ R.subgroupOf U
  let q : U →* W := QuotientGroup.mk' (R.subgroupOf U)
  obtain ⟨action, haction⟩ := exists_quotient_conjugation_action B U R hBU hBR hN
  have hWcard : Nat.card W = 4 := by
    have hh := (R.subgroupOf U).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hRU).toEquiv, hcard] at hh
    change Nat.card W * Nat.card R = 4 * Nat.card R at hh
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hh
  let fixedU : U := ⟨fixed, hfixedU⟩
  have hqne : q fixedU ≠ 1 := by
    intro heq
    apply hfixedR
    change fixedU ∈ R.subgroupOf U
    exact (QuotientGroup.eq_one_iff fixedU).mp heq
  have hqfix : ∀ automorphism ∈ action.range, automorphism (q fixedU) = q fixedU := by
    rintro automorphism ⟨actor, rfl⟩
    rw [haction]
    congr 1
    apply Subtype.ext
    have hcommute := mem_centralizer_singleton_iff.mp (hfix actor.property)
    change (actor : G) * fixed * (actor : G)⁻¹ = fixed
    rw [hcommute, mul_inv_cancel_right]
  have hrange : Nat.card action.range ≤ 2 :=
    card_mulAut_subgroup_le_two_of_fixed_point hWcard (q fixedU) hqne action.range hqfix
  let C := action.ker.map B.subtype
  have hCcard : Nat.card C = Nat.card action.ker := card_map_of_injective B.subtype_injective
  have hcount := action.ker.card_mul_index
  rw [Subgroup.index_ker] at hcount
  refine ⟨C, map_subtype_le _, ?_, ?_⟩
  · rw [hCcard]
    exact hcount.symm.le.trans (by nlinarith)
  · rw [commutator_comm]
    apply commutator_le.mpr
    rintro mover ⟨actor, hactor, rfl⟩ point hpoint
    let pointU : U := ⟨point, hpoint⟩
    have htrivial : action actor = 1 := hactor
    have hpointEq : action actor (q pointU) = q pointU := by
      rw [htrivial]
      rfl
    rw [haction] at hpointEq
    have hmem := (QuotientGroup.eq_iff_div_mem).mp hpointEq
    change (actor : G) * point * (actor : G)⁻¹ / point ∈ R at hmem
    simpa only [commutatorElement_def, div_eq_mul_inv, coe_subtype] using hmem

end Subgroup