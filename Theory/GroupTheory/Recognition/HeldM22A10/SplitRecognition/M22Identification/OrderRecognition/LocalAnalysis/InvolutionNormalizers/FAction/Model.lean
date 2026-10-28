module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.ModelSylow

/-!
# The finite automizer problem for Janko's second elementary sixteen

The two marked elements and the subgroup of eight automorphisms use the
actual Case II model. `FiniteSetup` separates the finite automorphism-group
calculation from its ambient realization. Its premises are proved from the
local data and z–d fusion in the sibling `Transport` module.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 2, pp.4–5.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction
open LocalModelDichotomy

/-- The source central involution, in F coordinates. -/
@[expose] public def pointZ : modelF := ⟨z 0, modelF_generators.1⟩
/-- The source actor involution, in F coordinates. -/
@[expose] public def pointD : modelF := ⟨d, modelF_generators.2.2.2⟩
/-- The exact conjugation image of the coordinate normalizer T. -/
@[expose] public def localAutomizer : Subgroup (MulAut modelF) := modelF.normalizerMonoidHom.range

/-- The coordinate Sylow subgroup induces eight automorphisms of F. -/
public theorem localAutomizer_card : Nat.card localAutomizer = 8 := by
  have h := card_eq_card_quotient_mul_card_subgroup modelF.normalizerMonoidHom.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange modelF.normalizerMonoidHom).toEquiv,
    normalizerMonoidHom_ker, modelF_centralizer,
    Nat.card_congr (subgroupOfEquivOfLe (H := modelF) le_normalizer).toEquiv,
    modelF_card] at h
  have hn : Nat.card (normalizer (modelF : Set TwistedModel)) = 128 := by
    rw [modelF_normalizer, modelT_card]
  rw [hn] at h
  change 128 = Nat.card localAutomizer * 16 at h
  omega

/-- Finite hypotheses for the automizer calculation in Janko's Lemma 2.
They record the local action and the two stabilizer constraints. They do not
assume either transitivity or an identification of the group. -/
public structure FiniteSetup (H : Subgroup (MulAut modelF)) : Prop where
  local_le : localAutomizer ≤ H
  stabilizer_z : ∀ a : MulAut modelF, a ∈ H →
    (a pointZ = pointZ ↔ a ∈ localAutomizer)
  card : ∃ m : ℕ, Odd m ∧ Nat.card H = 8 * m
  stabilizer_d : 8 ≤ Nat.card ↥(H ⊓ MulAction.stabilizer (MulAut modelF) pointD)

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction
