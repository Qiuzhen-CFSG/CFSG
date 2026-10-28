module

public import CFSG.Quasithin.Chapter1.Section02.Adequate.Chains
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Faithful
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.QuotientActions
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.ChiefFactors
public import CFSG.KnownSimple.CarrierCatalogue
public import Theory.GroupTheory.CComponent.CommutatorDichotomy

/-!
# Assembly of the equality-independent Section 1.2 deductions

This boundary uses the canonical local families and the full known-simple
carrier catalogue. The finite simple QTKE hypotheses supply the SQTK
quotients; condition (E) supplies characteristic two and subnormal inheritance.
The universally quantified A.3 results remain explicit pending their proofs.

The conditional structural assembly gives 1.2.1(1–3), the complete A.3.6
alternatives for the actual quotient image, its genuine omega actions, and
centrality of the two-chief factors above the intrinsic two-core. The
embedding deduction retains all twenty-two alternatives and relative
normality. The uniqueness deduction supplies all four clauses of 1.2.7,
with its former characteristic-two premise discharged.

The full general commutator dichotomy A.3.3(7) is proved in a narrow Theory
extension and discharges that premise in the index-two containment theorem.
The faithful-chain deduction verifies the Sylow and section-centralizer
identities needed for A.4.10, conditional on the earlier normalizer equality.

These are conditional deductions, not the completed adequate Section 1.2
theorem. In particular the rank assertions, embedding exclusions for chains,
A.4.10–11 specialization and the involution dichotomy still have to be
assembled. The extra centre–Frattini equality in the printed 1.2.1(4d)
is neither assumed nor asserted, and no homocyclic exponent is discarded.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
Appendix A.3, pp.43–48, and Section 1.2, pp.503–508.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.Adequate
universe u

/-- The earlier source assertions used by the structural and embedding
deductions. Their hypotheses concern arbitrary SQTK groups with trivial
two-core, rather than the desired Chapter 1 conclusions. -/
structure A3EarlierResults (κ : GroupClass.{u}) : Prop where
  structure36 : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK κ X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → A36Conclusion B
  commutation37 : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK κ X → pCore 2 X = ⊥ → ∀ B K : Subgroup X,
      B.IsCComponent → K.IsCComponent → B ≠ K → ⁅B, K⁆ = ⊥
  conjugates38 : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK κ X → pCore 2 X = ⊥ → ∀ B : Subgroup X, B.IsCComponent →
      B.Normal ∨ (normalizer (B : Set X)).index = 2 ∧ NonnormalCComponentModel B
  generation39 : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK κ X → pCore 2 X = ⊥ → cComponentLayer X = solvableResidual X
  embeddings312 : ∀ (X : Type u) [Group X] [Finite X],
    IsSQTK κ X → pCore 2 X = ⊥ → ∀ (S : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B

/-- The adequate structural output for one local group. This records the
proved scope 1.2.1(1–4), not the remaining rank clause (5). -/
structure LocalStructureConclusion (H : Type u) [Group H] [Finite H] : Prop where
  generation : cComponentLayer H = solvableResidual H
  commutation : ∀ B K : Subgroup H, B.IsCComponent → K.IsCComponent → B ≠ K →
    ⁅B, K⁆ ≤ B.pCoreIn 2 ⊓ K.pCoreIn 2 ∧ B.pCoreIn 2 ⊓ K.pCoreIn 2 ≤ pCore 2 H
  conjugates : ∀ B : Subgroup H, B.IsCComponent →
    B.Normal ∨ (Set.range fun g : H => B.map (MulAut.conj g).toMonoidHom).ncard = 2 ∧
      NonnormalCComponentModel (B ⧸ pCore 2 B)
  structureAndActions : ∀ B : Subgroup H, B.IsCComponent →
    A36Conclusion (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
      (¬ IsQuasisimple (B.map (QuotientGroup.mk' (pCore 2 H))) →
        CenterFrattiniSource.OmegaActionData (B.map (QuotientGroup.mk' (pCore 2 H))))
  chiefFactors : ∀ B : Subgroup H, B.IsCComponent →
    HasCentralPChiefFactors 2 (B ⧸ pCore 2 B)

variable {G : Type u} [Group G] [Finite G]

/-- Instantiate the local quotient and lift all structural clauses, retaining
the exact A.3.6 actions and the intrinsic chief-factor input for A.4.11. -/
theorem local_structure_of_A3
    (earlier : A3EarlierResults KnownSimple.IsKnownSimple.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G) : LocalStructureConclusion H := by
  have hQ := uniqueness_local_quotient_sqtk hG hH
  have hactions (B : Subgroup H) (hB : B.IsCComponent) :=
    proposition_1_2_1_four_earlier_with_actions earlier.structure36 hQ hB
  refine ⟨proposition_1_2_1_one_of_A_3_9 earlier.generation39 hQ,
    fun B K hB hK hne => proposition_1_2_1_two_of_A_3_7 earlier.commutation37 hQ hB hK hne,
    fun B hB => proposition_1_2_1_three_of_A_3_8 earlier.conjugates38 hQ hB,
    fun B hB => hactions B hB, ?_⟩
  intro B hB
  exact hasCentralTwoChiefFactors_cComponent_twoCore_quotient hB (hactions B hB).1.2

/-- Specialize the complete twenty-two-case embedding deduction to a genuine
local group of the finite simple QTKE ambient group. -/
theorem local_embeddings_of_A3
    (earlier : A3EarlierResults KnownSimple.IsKnownSimple.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G)
    (S : Sylow 2 H) {B : Subgroup H} (hB : B ∈ L H S) :
    ∃ K : Subgroup H, K.IsCComponent ∧ B ≤ K ∧
      (∀ D : Subgroup H, D.IsCComponent → B ≤ D → D = K) ∧
      A312Embedding (B.map (QuotientGroup.mk' (pCore 2 H)))
        (K.map (QuotientGroup.mk' (pCore 2 H))) ∧
      ((S : Subgroup H) ≤ normalizer (B : Set H) → K.Normal) :=
  lemma_1_2_4_of_A_3_12_A_3_8 earlier.embeddings312 earlier.conjugates38
    (uniqueness_local_quotient_sqtk hG hH) S hB

/-- The index-two containment deduction with the general A.3.3(7)
commutator premise discharged. Only the earlier SQTK generation theorem
is used from the structural classification. -/
theorem index_two_containment_of_A3
    (earlier : A3EarlierResults KnownSimple.IsKnownSimple.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G)
    (S : Sylow 2 H) {R B : Subgroup H}
    (hRS : R ≤ S) (hidx : R.relIndex (S : Subgroup H) = 2)
    (hB : B ∈ L H R) : ∃! K : Subgroup H, K.IsCComponent ∧ B ≤ K := by
  apply lemma_1_2_5_of_A_3_3_7_of_A_3_9
    (fun X _ _ D U hD => hD.commutator_le_radical_or_eq_iSup_conjugates U)
    earlier.generation39 (uniqueness_local_quotient_sqtk hG hH) S hRS hidx hB

/-- All four nonsolvable uniqueness clauses, with the 1.1 characteristic-two
obligation discharged. Only genuine A.3 earlier-source assertions remain. -/
theorem nonsolvable_uniqueness_of_A3
    (earlier : A3EarlierResults KnownSimple.IsKnownSimple.{u})
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B : Subgroup G} (hB : B ∈ LStar G T) :
    NonsolvableUniquenessConclusion T B := by
  apply nonsolvable_uniqueness_of_earlier (κ := KnownSimple.IsKnownSimple) ?_ hG T hB
  refine ⟨?_, earlier.conjugates38, ?_⟩
  · intro X _ _ hX hcore S B hB
    obtain ⟨K, hK, hBK, hu, _⟩ := earlier.embeddings312 X hX hcore S B hB
    exact ⟨K, ⟨hK, hBK⟩, fun D hD => hu D hD.1 hD.2⟩
  · intro X _ _ hX S
    exact lemma_1_1_4_6 S (hX.evenCharacteristic S)

end CFSG.Quasithin.Chapter1.Section02.Adequate
