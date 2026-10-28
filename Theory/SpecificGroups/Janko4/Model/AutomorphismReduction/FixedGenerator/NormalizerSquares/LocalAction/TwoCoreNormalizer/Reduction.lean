module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCore
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearModel

/-!
# Reducing the J₄ two-core normalizer calculation to a binary matrix action

Let R be the image of the literal centralizer C in Aut(Q), for Q = O₂(C).
Suppose a homomorphism ρ from Aut(Q) to GL₁₂(2) has kernel contained in
Inn(Q) and maps R onto the explicitly generated group in `LinearModel`.
Since Inn(Q) ≤ R, R is the full preimage of its image under ρ. Consequently,
self-normalization of that matrix group implies self-normalization of R.
Surjectivity of ρ onto GL₁₂(2) is unnecessary.

The proposed ρ is the action on the central quotient of an extraspecial Q,
after choosing binary coordinates. Neither that concrete comparison nor
the matrix normalizer calculation is proved here. In particular this module
does not yet prove `localTwoCoreActionSelfNormalizer` from centralizer control.

Source motivation: GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. The table gives the local structure;
it does not assert the self-normalizer calculation required here.
-/

public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares

/-- A concrete quotient action comparison. Its kernel and image clauses
must both be proved for the literal Q and the specified matrix generators. -/
@[expose] def LocalTwoCoreLinearComparison : Prop :=
  ∃ ρ : MulAut involutionTwoCore →* TwoCoreLinearModel.Matrix12ˣ,
    ρ.ker ≤ (MulAut.conj (G := involutionTwoCore)).range ∧
    involutionTwoCoreAction.range.map ρ = TwoCoreLinearModel.actionGroup

private theorem normalizer_le_of_map {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (f : G →* K) (hker : f.ker ≤ H)
    (hnorm : Subgroup.normalizer (H.map f : Set K) ≤ H.map f) :
    Subgroup.normalizer (H : Set G) ≤ H := by
  calc
    Subgroup.normalizer (H : Set G) ≤
        (Subgroup.normalizer (H.map f : Set K)).comap f :=
      Subgroup.map_le_iff_le_comap.mp (H.le_normalizer_map f)
    _ ≤ (H.map f).comap f := Subgroup.comap_mono hnorm
    _ = H := Subgroup.comap_map_eq_self hker

/-- The kernel bound makes the local action image the entire preimage of
the specified binary matrix group. -/
theorem involutionTwoCoreAction_range_eq_comap
    (ρ : MulAut involutionTwoCore →* TwoCoreLinearModel.Matrix12ˣ)
    (hker : ρ.ker ≤
      (MulAut.conj (G := involutionTwoCore)).range)
    (himage : involutionTwoCoreAction.range.map ρ = TwoCoreLinearModel.actionGroup) :
    involutionTwoCoreAction.range = TwoCoreLinearModel.actionGroup.comap ρ := by
  rw [← himage]
  exact (Subgroup.comap_map_eq_self
    (hker.trans inner_le_involutionTwoCoreAction_range)).symm

/-- Transfer a proved matrix normalizer calculation through a proved
comparison. These two additional premises remain separate obligations. -/
theorem localTwoCoreActionSelfNormalizer_of_linearComparison
    (hcomparison : LocalTwoCoreLinearComparison)
    (hnorm : Subgroup.normalizer
      (TwoCoreLinearModel.actionGroup : Set TwoCoreLinearModel.Matrix12ˣ) ≤
        TwoCoreLinearModel.actionGroup) : LocalTwoCoreActionSelfNormalizer := by
  obtain ⟨ρ, hker, himage⟩ := hcomparison
  apply normalizer_le_of_map involutionTwoCoreAction.range ρ
    (hker.trans inner_le_involutionTwoCoreAction_range)
  rwa [himage]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares
