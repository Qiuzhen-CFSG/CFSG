module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Max2Stability
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max1.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max4.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Cubic
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.MathieuTransport

/-!
# The adequate actor-wise J₄ reduction from local models

The permuting pair product is solvable and proper, so it lies in a maximal
proper overgroup containing the original Sylow subgroup. Apply the existing
maximal-Sylow-overgroup cover with its actual max1, max2 and max4 equivalences.
The local characteristic-subgroup arguments make these embeddings stable
under the ambient pair actors, including their action on the local Sylow.

The max1 and max2 calculations must construct invariant Frattini subgroups.
The max4 branch keeps its full compatible placement conclusion. The final
consumer bridge uses the max4 quotient only on that surviving branch.

The maximal cover, max1 Sylow characteristicity, max4 normal characteristic
subgroup, and two local reducibility calculations remain explicit inputs.
This is conditional assembly, not the unconditional adequate reduction or
the final J₄ exclusion. The old universal placement contracts remain separate.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511/PDF p.528;
see `docs/quasithin-proof-basis.md`.
-/

public section

set_option backward.isDefEq.respectTransparency true

open Subgroup
open Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

attribute [local irreducible] Janko4.modelGroup max4Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
open Max4Conjugacy.SylowCover

namespace Adequate

/-- The max1 core characteristicity input controls all ambient pair actors
on an actual maximal embedding, without assuming an ambient normalizer equality. -/
theorem max1_stable (hchar : Max1SylowCoreCharacteristic)
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model]
    (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model)
    (hM : IsCoatom M) (hSM : S.toSubgroup ≤ M)
    (e : M ≃* Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (b : MulAut Janko4.Model) (hb : ∀ x, b x ∈ S ↔ x ∈ S) :
    ∀ x, b x ∈ M ↔ x ∈ M := by
  exact stable_coatom_of_sylow_characteristic_normal
    (Janko4.Cardinality.localKernel Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (Janko4.LocalStructure.localKernel_ne_bot _ _)
    (IsPGroup.of_card (n := 11) (Janko4.Cardinality.localKernel_card _ _))
    hchar S M hM hSM e b hb

/-- A local normal subgroup characteristic in Sylows controls max4 actors. -/
theorem max4_stable (hlocal : Max4SylowCharacteristicNormal)
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model]
    (S : Sylow 2 Janko4.Model) (M : Subgroup Janko4.Model)
    (hM : IsCoatom M) (hSM : S.toSubgroup ≤ M) (e : M ≃* max4Subgroup)
    (b : MulAut Janko4.Model) (hb : ∀ x, b x ∈ S ↔ x ∈ S) :
    ∀ x, b x ∈ M ↔ x ∈ M := by
  obtain ⟨A, hn, hne, hp, hchar⟩ := hlocal
  let _ := hn
  exact stable_coatom_of_sylow_characteristic_normal A hne hp hchar S M hM hSM e b hb

/-- Solvability of the permuting product places the entire pair in a maximal
proper subgroup, retaining both odd-complement cases. -/
theorem exists_maximal_pair_overgroup [Finite Janko4.Model]
    (S : Sylow 2 Janko4.Model) (R : Subgroup Janko4.Model) (h : PairInput S R) :
    ∃ M : Subgroup Janko4.Model, IsCoatom M ∧ S.toSubgroup ≤ M ∧ R ≤ M := by
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (R ⊔ S.toSubgroup)).resolve_left
    (EvenRankTwo.product_ne_top h)
  exact ⟨M, hM, le_sup_right.trans hle, le_sup_left.trans hle⟩

end Adequate

/-- Conditional assembly retaining every actor. The five explicit structural
inputs must be proved before claiming the unconditional adequate alternative. -/
theorem adequateMaximalFourPairActions_of_local_models
    (hcover : CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.MaximalSylowCover)
    (hchar1 : Max1SylowCoreCharacteristic)
    (hchar4 : Max4SylowCharacteristicNormal)
    (hmax1 : Adequate.LocalModelPairReducibility
      (Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four))
    (hmax2 : Adequate.LocalModelPairReducibility sourceSubgroup) :
    AdequateMaximalFourPairActions := by
  intro _ _ _ S R h D hD htwo
  obtain ⟨M, hM, hSM, hRM⟩ := Adequate.exists_maximal_pair_overgroup S R h
  rcases hcover S M hM hSM with he | he | he
  · obtain ⟨e⟩ := he
    exact Or.inl (hmax1 S R h M hM hSM hRM e D hD htwo
      (Adequate.compatibleSylowActions_of_stable S.toSubgroup R M hRM D hD
        (Adequate.max1_stable hchar1 S M hM hSM e)))
  · obtain ⟨e⟩ := he
    exact Or.inl (hmax2 S R h M hM hSM hRM e D hD htwo
      (Adequate.compatibleSylowActions_of_stable S.toSubgroup R M hRM D hD
        (Adequate.max2_stable S M hM hSM e)))
  · obtain ⟨e⟩ := he
    have hlifts := Adequate.compatibleSylowActions_of_stable S.toSubgroup R M hRM D hD
      (Adequate.max4_stable hchar4 S M hM hSM e)
    refine Or.inr ⟨M, hRM, hSM, ⟨e⟩, ?_⟩
    intro a ha
    obtain ⟨c, _, hc⟩ := hlifts a ha
    exact ⟨c, hc⟩


/-- The max4 quotient is used only on the placement branch of the adequate
alternative. Its construction remains the source assembly owner’s obligation. -/
theorem pairReducible_of_adequateMaximalFour
    (hquot : MaximalFourQuotient) (hactions : AdequateMaximalFourPairActions)
    [Finite Janko4.Model] [IsSimpleGroup Janko4.Model] [Group.IsPerfect Janko4.Model]
    (S : Sylow 2 Janko4.Model) (R : Subgroup Janko4.Model) (h : PairInput S R) :
    PairReducible S.toSubgroup R := by
  intro D hD htwo
  rcases hactions S R h D hD htwo with hred | ⟨M, hRM, _, ⟨f⟩, ha⟩
  · exact hred
  · obtain ⟨e⟩ := hquot
    exact invariantFrattiniSubgroup_of_localQuotient D h.oddComplement hRM
      ((QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e) ha

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction
