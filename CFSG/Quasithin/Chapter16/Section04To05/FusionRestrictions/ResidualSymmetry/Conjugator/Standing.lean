module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.ActorGeometry
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The standing quasithin rank obstruction

The full standing hypothesis contributes a precise obstruction to any proposed
unequal-actor construction: an actual elementary abelian odd-prime subgroup of
order `p²`, together with an independent commuting order-`p` actor in its
two-local normalizer, gives odd-prime rank at least three.  The source
two-local formulation of quasithinness then rules this out.

This is an assembly diagnostic for the selected-conjugator comparison.  It
does not assert that unequal residuals always produce the displayed witness;
that model-dependent construction remains the missing source input for
normalization of the selected `g`.

The conditional assembly at the end separates the genuine E2 alternatives.
Its three witness producers are outstanding mathematical obligations, not
fields of the standing hypothesis and not proved classification statements.

The class parameter is kept generic so the extension imports only the genuine
standing-hypothesis interface; the source owner instantiates it with
`KnownSimple.IsKnownSimple`.

Source: Hypothesis 16.1.1 and Corollary A.2.6, printed pp.1169--1170 and 34.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator

variable {G : Type*} [Group G] [Finite G]

/-- An actual rank-three witness inside a two-local contradicts the standing
quasithin hypothesis.  The subgroup `E` and actor `x` are retained as genuine
ambient subgroups/elements; no residual or model label is used as a proxy for
this witness. -/
theorem false_of_standing_rank_three_witness
    {κ : GroupClass} (hG : Hypothesis1611 κ G)
    {Q E : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hQ : Q ≠ ⊥) (hQp : IsPGroup 2 Q)
    (hEN : E ≤ normalizer (Q : Set G))
    (hE : IsElementaryAbelian p E) (hcard : Nat.card E = p ^ 2)
    {x : G} (hxN : x ∈ normalizer (Q : Set G)) (hxp : orderOf x = p)
    (hxE : x ∉ E) (hfix : E ≤ centralizer ({x} : Set G))
    (hpodd : Odd p) : False := by
  let N := normalizer (Q : Set G)
  let E0 : Subgroup N := E.subgroupOf N
  let x0 : N := ⟨x, hxN⟩
  let : IsElementaryAbelian p E := hE
  let : IsElementaryAbelian p E0 := IsElementaryAbelian.subgroupOf hEN
  have hE0card : Nat.card E0 = p ^ 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv).trans hcard
  have hx0p : orderOf x0 = p := (orderOf_coe x0).symm.trans hxp
  have hx0E0 : x0 ∉ E0 := by
    intro hx
    exact hxE hx
  have hfix0 : E0 ≤ centralizer ({x0} : Set N) := by
    intro y hy
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hfix hy)
  have hlo : 3 ≤ primeRank p N :=
    IsElementaryAbelian.primeRank_ge_of_fixed_join E0 x0 hx0p hx0E0 hfix0 hE0card
  have hlocal : IsTwoLocal N := ⟨Q, hQ, hQp, rfl⟩
  have hhi := Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG.quasithin N hlocal p
    (Fact.out : p.Prime) hpodd
  omega

/-- Apply the standing bound to the concrete output of a model construction. -/
theorem OddRankThreeWitness.false_of_standing {κ : GroupClass}
    (w : OddRankThreeWitness G) (hG : Hypothesis1611 κ G) : False := by
  let : Fact w.p.Prime := ⟨w.prime⟩
  exact false_of_standing_rank_three_witness hG w.Q_ne w.Q_two w.E_normalizes
    w.E_elementary w.E_card w.x_normalizes w.x_order w.x_independent w.x_centralizes w.odd

/-- Conditional assembly across all three E2 alternatives. Each producer must
construct the displayed ambient rank witness from the unequal residuals in its
own model family. This theorem does not discharge any of those producers. -/
theorem ResidualInputs.normalizes_of_model_witnesses
    {κ : GroupClass} (hG : Hypothesis1611 κ G)
    {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (d : ResidualInputs T z L g R)
    (hlie : IsEvenTypeLieComponent L →
      modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
        modifiedCentralizerResidual L (MulAut.conj g z) →
      Nonempty (OddRankThreeWitness G))
    (hodd : (ClassicalGroup.IsPSL L 3 3 ∨
        ∃ p : ℕ, IsFermatOrMersennePrime p ∧
          ClassicalGroup.IsPSL L 2 p) →
      modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
        modifiedCentralizerResidual L (MulAut.conj g z) →
      Nonempty (OddRankThreeWitness G))
    (hsporadic : IsEvenTypeSporadicQuotient (L ⧸ pCore 2 L) →
      modifiedCentralizerResidual L (MulAut.conj g⁻¹ z) ≠
        modifiedCentralizerResidual L (MulAut.conj g z) →
      Nonempty (OddRankThreeWitness G)) :
    g ∈ normalizer (modifiedCentralizerResidual L (MulAut.conj g z) : Set G) := by
  apply (normalizes_iff_inverse_actor_residual d.setup d.transport d.common.1 d.common.2).mpr
  by_contra hne
  have hw : Nonempty (OddRankThreeWitness G) := by
    rcases hG.evenType.components z L d.setup.involution d.setup.component with
      hL | hL | hL | hL
    · exact hlie hL hne
    · exact hodd (Or.inl hL) hne
    · exact hodd (Or.inr hL) hne
    · exact hsporadic hL hne
  exact hw.some.false_of_standing hG

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator
