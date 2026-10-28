module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.FactorBounds

/-!
# The literal ending-factor catalogue for DGS 8.2

The factor-module construction and its model estimates are useful only after
the actual quotient at the ending vertex has been split into the source
catalogue.  This module performs that split on the original reduced F1.11
graph.  Linear endpoints give the first index bound; Suzuki, dihedral and
large unitary endpoints give the square bound.  The two field-two unitary
rows are retained as the only unresolved alternatives.  No conclusion about
the critical distance or the starting quotient is built into this dispatcher.

Source: DGS, *Groups and Graphs* (1985), 8.2, printed p.135; the quotient
models are the literal alternatives of F.1.1(c), and the factor estimates are
the corrected 5.12 applications proved in `FactorBounds`.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The complete literal ending-factor split in 8.2.  Every bound is on the
original core and centralizer indices; the final disjunct records precisely
the field-two unitary alternatives rather than silently dropping them. -/
theorem reduced_ending_factor_bound_or_small_unitary
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {D : Type u} [Group D] [Finite D]
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')) ≃* D)
    (hm : IsRankOneModel D) :
    let Γ := Reduction.reducedFamily L S₀
    (Q Γ a').relIndex (Z Γ a) ≤
        (centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) ∨
      ((Q Γ a').relIndex (Z Γ a)) ^ 2 ≤
        (centralizer (Z Γ a : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) ∨
      (ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2) := by
  let Γ := Reduction.reducedFamily L S₀
  dsimp only
  cases hm with
  | linear n hn hi =>
      obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := hi
      let := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hF)
      let f := eF.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
        ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩).symm
      left
      exact reduced_ending_linear_constituent_bound h hc hab hd hb hcomm hn hF (e.trans f)
  | suzuki m hi =>
      right
      left
      exact reduced_ending_suzuki_constituent_bound h hc hab hd hb hcomm m (e.trans hi.some)
  | projective_unitary n hn hi =>
      by_cases hn2 : 2 ≤ n
      · obtain ⟨F, _, _, J, hF, hconj, ⟨eJ⟩⟩ := hi
        right
        left
        exact reduced_ending_projective_unitary_constituent_bound h hc hab hd hb hcomm
          J hn2 hF hconj (e.trans eJ)
      · have hn1 : n = 1 := by omega
        right
        right
        exact Or.inl (by simpa only [hn1, pow_one] using hi)
  | special_unitary n hn hi =>
      by_cases hn2 : 2 ≤ n
      · obtain ⟨F, _, _, J, hF, hconj, ⟨eJ⟩⟩ := hi
        right
        left
        exact reduced_ending_special_unitary_constituent_bound h hc hab hd hb hcomm
          J hn2 hF hconj (e.trans eJ)
      · have hn1 : n = 1 := by omega
        right
        right
        exact Or.inr (by simpa only [hn1, pow_one] using hi)
  | dihedral hi =>
      right
      left
      exact reduced_ending_dihedral_constituent_bound h hc hab hd hb hcomm (e.trans hi.some)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
