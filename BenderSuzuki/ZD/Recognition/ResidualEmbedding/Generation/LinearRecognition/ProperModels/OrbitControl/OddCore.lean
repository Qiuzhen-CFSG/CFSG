module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.Foundations
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionThree.Local

/-!
# Z-star control for the residual pair stabilizer

Apply the point-swapping Z-star theorem at the identity coset of `M`.
The two-point stabilizer is exactly `D = M ∩ Mᵗ`, and its odd core is
formed inside `D` before mapping into the ambient group.

Source: GLS, Volume 4, Chapter 2, Propositions 3.5 and 3.7, pp.29–30.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
private theorem fixes_mk_iff (x b : G) :
    x • (QuotientGroup.mk b : G ⧸ M) = QuotientGroup.mk b ↔ b⁻¹ * x * b ∈ M := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
  constructor
  · intro h
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using M.inv_mem h
  · intro h
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using M.inv_mem h

/-- The local Z-star consequence for the actual two-point stabilizer `D`.
The odd core is relative to `D`, with its ambient image stated explicitly. -/
public theorem residualPairStabilizer_commutator_le_oddCore
    (h : IsProductDisconnected Z M) {t : G} (ht : t ∈ Z) (htM : t ∉ M) :
    ⁅residualPairStabilizer M t, Subgroup.zpowers t⁆ ≤
      (pPrimeCore 2 (residualPairStabilizer M t)).map
        (residualPairStabilizer M t).subtype := by
  let beta : G ⧸ M := QuotientGroup.mk 1
  have hm : t • beta ≠ beta := by
    intro he
    apply htM
    have hh := (fixes_mk_iff t 1).mp he
    simpa using hh
  apply sectionThree_swapping_core h ht beta hm
  · intro d hd
    constructor
    · apply MulAction.mem_stabilizer_iff.mpr
      apply (fixes_mk_iff d 1).mpr
      simpa using hd.1
    · rw [show t • beta = (QuotientGroup.mk t : G ⧸ M) by
        simp [beta, MulAction.Quotient.smul_mk, smul_eq_mul]]
      rw [conjugateCoset_stabilizer,
        (h.involutions t ht).inv_eq_self]
      exact hd.2
  · exact inf_rightConjugate_mem_normalizer_of_isInvolution
      M (h.involutions t ht)

end BenderSuzuki.ZD
