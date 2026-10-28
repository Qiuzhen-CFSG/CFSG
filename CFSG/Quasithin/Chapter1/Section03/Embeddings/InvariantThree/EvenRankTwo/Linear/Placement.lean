module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement.Transport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement.Borel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement.ProperParabolic
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement.ParabolicBorel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Placement.ScalarCover

/-!
# Assembly of the ternary PSL₃ placement

The actual central quotient is conjugated so that the projected Sylow is UT₃.
Its three-complement has order at most 27 and solvable product with UT₃.
The product has a nontrivial two-core, whose normalizer is an actual two-local
overgroup. The fixed-space argument places it in a conjugate parabolic, and
the rank-one Levi argument places it in the Borel. Sylow normalization then
lifts through the center, without any multiplier hypothesis.

For abelianness, universality constructs a commuting surjection from SL₃,
using the explicitly retained earlier-source input `UniversalMultiplierInput`.
This lifts the three-complement to the matrix Borel, where the diagonal
calculation proves it abelian. The input states I.1.3 for actual universal
perfect central covers: cyclic three or trivial in the ordinary cases, and
C₄ × C₄ × C₃ for PSL₃(4). Both geometric placement and the scalar-cover
comparison are proved; the multiplier theorem itself remains a parameter.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), and I.1.3, printed p.407 (PDF p.418), `refs/quasithin.pdf`.
-/

public section
open Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement

/-- A small ternary complement permuting with the full UT₃ Sylow lies in its Borel.
The nontrivial two-core supplies the parabolic witness. This includes F₄. -/
theorem projective_le_borel {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2^f)
    {B : Subgroup PSL(3,F)} (h : ProjectiveInput F B) : B ≤ borel F :=
  le_borel_of_parabolic F hf hF B h (projective_product_parabolic hf hF h)

/-- Borel placement of the projected complement lifts to normalization of the actual Sylow. -/
theorem normalizes_of_model_borel {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} {F : Type*} [Field F] [Finite F]
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (e : Q ⧸ center Q ≃* PSL(3,F))
    (hS : (S : Subgroup Q).map (modelProjection e) = unipotent F)
    (hB : R.map (modelProjection e) ≤ borel F) :
    R ≤ normalizer (S : Set Q) := by
  have hn : R.map (modelProjection e) ≤
      normalizer ((S : Subgroup Q).map (modelProjection e)) := by
    rw [hS, normalizer_unipotent F hf hF]
    exact hB
  rw [map_le_iff_le_comap, normalizer_comap_of_central S (modelProjection e)
    (modelProjection_surjective e) (by rw [modelProjection_ker])] at hn
  exact hn

/-- The source complement normalizes the actual Sylow for every field order at least four.
No multiplier calculation or assumed geometric containment is needed. -/
theorem normalizes {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 (2^f)) :
    R ≤ normalizer (S : Set Q) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  obtain ⟨e', hS⟩ := exists_sylow_coordinates S (by omega) hF e
  exact normalizes_of_model_borel (by omega) hF e' hS
    (projective_le_borel hf hF (projectiveInput_of_pair h e' hS))

/-- Conditional assembly from actual Borel placement and an actual scalar-cover map.
Neither remaining model premise is asserted by this theorem. -/
theorem placement_of_model_inputs {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 (2^f))
    (hplacement : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2^f →
      ∀ B : Subgroup PSL(3,F), ProjectiveInput F B → B ≤ borel F)
    (hcover : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2^f →
      ∀ e : Q ⧸ center Q ≃* PSL(3,F),
        ∃ k : SL(3,F) →* Q, Function.Surjective k ∧
          (modelProjection e).comp k = projection F) :
    R ≤ normalizer (S : Set Q) ∧ IsMulCommutative R := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  obtain ⟨e', hS⟩ := exists_sylow_coordinates S (by omega) hF e
  have hB := hplacement F hF _ (projectiveInput_of_pair h e' hS)
  obtain ⟨k, hk, hfac⟩ := hcover F hF e'
  exact ⟨normalizes_of_model_borel (by omega) hF e' hS hB,
    threeSubgroup_commutative_of_scalar_cover F hF R h.oddComplement.isPGroup
      (modelProjection e') k hk hfac hB⟩

/-- The binary PSL₃ placement, including central covers and the field of order four.
The only retained premise beyond the source pair and its model is the exact
universal multiplier implication of I.1.3. The parabolic witness, Borel
containment and commuting SL₃ surjection are all constructed. -/
theorem placement_of_universalMultiplierInput {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 (2^f))
    (hI : ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2^f →
      ScalarCover.UniversalMultiplierInput F f) :
    R ≤ normalizer (S : Set Q) ∧ IsMulCommutative R := by
  apply placement_of_model_inputs h hf hmodel
  · intro F _ _ hF B hB
    exact projective_le_borel hf hF hB
  · intro F _ _ hF e
    exact ScalarCover.exists_scalar_cover h hf hF (hI F hF) e

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Placement
