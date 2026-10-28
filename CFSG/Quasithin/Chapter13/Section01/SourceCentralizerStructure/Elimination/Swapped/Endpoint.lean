module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Action
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Contracts

/-!
# The order-p pair endpoint in original 13.1.12(3)

The actual canonical radical quotient is elementary of order p² or
extraspecial of order p³. A complement of order p² excludes the latter
and therefore has zero Frattini subgroup. Every order-p subgroup is then
proper with nonzero Frattini trace, so the proved perfect normalizer-action
obstruction applies. The component geometry must still construct this pair.

Source: Aschbacher--Smith, 13.1.12(3), printed p.875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter1.RadicalActions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- An actual order-p pair in the order-p² complement contradicts the
canonical radical normalizer action. -/
theorem Context.false_of_normalizer_line_pair (h : Context T L p)
    (P : Sylow p (XiP p L))
    (hcard : Nat.card ((P : Subgroup (XiP p L)).map (XiP p L).subtype) = p ^ 2)
    (pair : NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p) : False := by
  let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  change Nat.card P₀ = p ^ 2 at hcard
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun D _ _ => ChapterA.Section02.theoremA_knownSimple (G := D))
    (fun D _ _ => ChapterA.Section02.theoremC_knownSimple (G := D))
  have hQ := uniqueness_local_quotient_sqtk h.hypothesis.simpleQTKE h.maximal.1.1.2.2
  have hq := (XiP_oddQuotient_of_A36 h36 h.maximal.1.1 hQ h.nonquasisimple h.odd h.divides).2
  have hP := hq.of_mulEquiv (ambientSylowQuotientEquiv h.odd hq.isPGroup P).symm
  change XiOddQuotient p P₀ at hP
  have hPhi : frattini P₀ = ⊥ := by
    let : Fact (IsPGroup p P₀) := ⟨hP.isPGroup⟩
    rcases hP with ⟨he,_⟩ | ⟨_,hc,_⟩
    · let := he
      exact frattini_eq_bot_of_isElementaryAbelian (p := p)
    · have hlt := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (show 2 < 3 by decide)
      omega
  apply h.no_normalizer_pair P pair.first pair.second pair.permuted
  · intro hPA
    have he : P₀ = pair.first := le_antisymm hPA pair.first_le
    have hc := congrArg (fun A : Subgroup G => Nat.card A) he
    have hp := (Fact.out : p.Prime).two_le
    rw [hcard,pair.first_card] at hc
    nlinarith
  · intro ht
    change P₀ ⊓ pair.first ≤ (frattini P₀).map P₀.subtype at ht
    rw [hPhi,Subgroup.map_bot,inf_eq_right.mpr pair.first_le] at ht
    have he := bot_unique ht
    have hc := pair.first_card
    rw [he,Subgroup.card_bot] at hc
    exact (Fact.out : p.Prime).ne_one hc.symm

/-- The geometric endpoint for the actual exchanged-component data. -/
theorem Context.false_of_swapped_line_pair (h : Context T L p)
    {u : G} {K : Subgroup G} (P : Sylow p (XiP p L))
    (d : SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype))
    (pair : NormalizerLinePair L ((P : Subgroup (XiP p L)).map (XiP p L).subtype) p) : False := by
  exact h.false_of_normalizer_line_pair P
    ((Nat.card_congr d.plane.some.toEquiv).trans (XiEmbedding.plane_card p)) pair

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
