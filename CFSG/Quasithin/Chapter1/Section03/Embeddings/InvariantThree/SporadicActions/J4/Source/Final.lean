module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Source.NoEight
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Source.NormalizerModels
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Source.LocalReducers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Source.ActorStability
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.Janko
/-!
# The original intrinsic p=3 J₄ pair exclusion

For the original permuting pair, the solvable product has nontrivial two-core.
Its canonical central Sylow closure is minimal elementary normal. The checked
literal catalogue and the elementary-eight obstruction leave max1, the max2
involution centralizer, or a conjugate of max4. Actual normalizer equalities
make each chosen local group stable under the original pair automorphisms.
The proved local quotient calculations then construct the required proper
nonzero invariant Frattini subgroup for each two-group actor.

Finally the actual J₄ odd-primary multiplier theorem makes the center of a
quasisimple source group a two-group; its assumed trivial two-core eliminates
that center. The resulting equivalence transports the original pair and
actors through the given central quotient. No maximal-Sylow-overgroup cover,
small-prime generation assertion, or universal max4 placement is assumed.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528).
The explicit matrix normalizer/candidate comparisons are those of the cited
A.3.12 local analysis, retained in the imported source descendants.
-/

public section
open Subgroup
open Janko4 Janko4.Cardinality Janko4.LocalStructure.SymmetricLinear
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup max4Subgroup
open J4Reduction

namespace J4Reduction.Source
variable [Finite Model] [IsSimpleGroup Model] [Group.IsPerfect Model]

/-- Every original actor in literal max1 has a proper invariant Frattini subgroup. -/
theorem pairReducible_of_literal_max1 {S : Sylow 2 Model} {R : Subgroup Model}
    (h : PairInput S R)
    (hS : S.toSubgroup ≤ max1Subgroup matrixA_mul_self matrixB_pow_four)
    (hR : R ≤ max1Subgroup matrixA_mul_self matrixB_pow_four) : PairReducible S.toSubgroup R := by
  intro D hD hp
  exact Adequate.max1_actorReducible_of_compatible S R h _ hS hR (MulEquiv.refl _) D hp
    (Adequate.compatibleSylowActions_of_stable _ _ _ hR D hD
      (literal_max1_stable S hS))

omit [IsSimpleGroup Model] [Group.IsPerfect Model] in
/-- The actual max4 quotient excludes the original pair action. -/
theorem pairReducible_of_literal_max4 {S : Sylow 2 Model} {R : Subgroup Model}
    (h : PairInput S R) (hS : S.toSubgroup ≤ max4Subgroup) (hR : R ≤ max4Subgroup) :
    PairReducible S.toSubgroup R := by
  intro D hD _hp
  have hact := Adequate.compatibleSylowActions_of_stable _ _ _ hR D hD
    (literal_max4_stable S hS)
  apply invariantFrattiniSubgroup_of_localQuotient D h.oddComplement hR
    max4QuotientEquiv
  intro a ha
  obtain ⟨c, _, hc⟩ := hact a ha
  exact ⟨c, hc⟩

/-- The order-two closure branch uses its literal involution-centralizer equivalence. -/
theorem pairReducible_of_closure_two {S : Sylow 2 Model} {R : Subgroup Model}
    (h : PairInput S R)
    (hc : Nat.card (elementaryClosure S (R ⊔ S.toSubgroup) le_sup_right) = 2) :
    PairReducible S.toSubgroup R := by
  let H := R ⊔ S.toSubgroup
  let M := normalizer (elementaryClosure S H le_sup_right : Set Model)
  have hHM : H ≤ M := overgroup_le_elementaryClosure_normalizer S H le_sup_right
  have hS : S.toSubgroup ≤ M := le_sup_right.trans hHM
  have hR : R ≤ M := le_sup_left.trans hHM
  obtain ⟨e⟩ := normalizer_equiv_max2_of_closure_card_two S H le_sup_right hc
  intro D hD _hp
  exact Adequate.max2_actorReducible_of_compatible S R h M hS hR e D
    (Adequate.compatibleSylowActions_of_stable _ _ _ hR D hD
      (closure_two_normalizer_stable S H le_sup_right (product_twoCore_ne_bot h) hc))

omit [IsSimpleGroup Model] [Group.IsPerfect Model] in
/-- Actual ambient conjugation transports both original pair members and all actors. -/
theorem pairReducible_of_conjugate_max4 {S : Sylow 2 Model} {R : Subgroup Model}
    (h : PairInput S R) (g : Model)
    (hle : (R ⊔ S.toSubgroup) ≤ max4Subgroup.map (MulAut.conj g).toMonoidHom) :
    PairReducible S.toSubgroup R := by
  let e := (MulAut.conj g).symm
  have hle' (A : Subgroup Model) (hA : A ≤ R ⊔ S.toSubgroup) :
      A.map e.toMonoidHom ≤ max4Subgroup := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hle (hA hx)
    have hey : e x = y := by rw [← he]; exact (MulAut.conj g).symm_apply_apply y
    change e x ∈ max4Subgroup
    rwa [hey]
  apply pairReducible_of_map e S.toSubgroup R
  exact pairReducible_of_literal_max4 (pairInput_map e h)
    (hle' S.toSubgroup le_sup_right) (hle' R le_sup_left)

/-- The fixed Sylow catalogue discharges every original pair actor. -/
theorem pairReducible_of_fixed_sylow {S : Sylow 2 Model} {R : Subgroup Model}
    (h : PairInput S R) (hS : S.toSubgroup = OuterReduction.OddIndex.twoSubgroup) :
    PairReducible S.toSubgroup R := by
  rcases product_elementaryClosure_three_cases h hS with hm | h1 | h2
  · exact pairReducible_of_literal_max1 h (le_sup_right.trans hm) (le_sup_left.trans hm)
  · apply pairReducible_of_closure_two h
    rw [h1, KernelOrders.pureKernelCatalogue.2 1]
    rfl
  · apply pairReducible_of_conjugate_max4 h MatrixNormalizerBounds.ThirdConjugacy.conjugator
    have hn := overgroup_le_elementaryClosure_normalizer S (R ⊔ S.toSubgroup) le_sup_right
    rw [h2] at hn
    exact hn.trans candidate_two_normalizer_le_max4_conjugate

end J4Reduction.Source

/-- The unconditional pair exclusion on the actual J₄ carrier. -/
theorem j4_carrierPairExclusion : CarrierPairExclusion Model := by
  intro _ _ _ S R h
  let T : Sylow 2 Model := Sylow.ofCard OuterReduction.OddIndex.twoSubgroup
    (OuterReduction.OddIndex.twoSubgroup_card.trans
      ((OuterReduction.OddIndex.ambient_sylow_card S).symm.trans S.card_eq_multiplicity))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model S T
  let e := MulAut.conj g
  have hm : (S.mapSurjective (f := e.toMonoidHom) e.surjective).toSubgroup =
      OuterReduction.OddIndex.twoSubgroup := congrArg Sylow.toSubgroup hg
  exact pairReducible_of_map e S.toSubgroup R
    (Source.pairReducible_of_fixed_sylow (pairInput_map e h) hm)

/-- The original quasisimple source pair is reducible through its given J₄ central quotient. -/
theorem j4_pairReducible {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (e : (Q ⧸ center Q) ≃* Model) : PairReducible S.toSubgroup R := by
  let _ := h.quasisimple
  exact pairReducible_of_centralQuotient h e
    (Janko4.OddPrimary.center_isPGroup_of_quotient_equiv e) j4_carrierPairExclusion

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
