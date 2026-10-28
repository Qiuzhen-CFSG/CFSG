module

public import Stellmacher.PushingUp.CriticalPairActionInputs
public import Stellmacher.PushingUp.CriticalPairFixedSpace
public import Stellmacher.PushingUp.CriticalPairReconstruction

/-!
# The critical-pair `SL₂(2)` module theorem

This module proves Stellmacher, *Pushing up*, Arch. Math. 46 (1986), Lemma
(2.2), journal p.11, under the standing `p = 2`, `n = 1` hypotheses.  For a
positive-distance critical pair `(a,a')`, it proves that
`Z_{a'} O₂(G_a)` is Sylow in `G_a`, identifies the faithful quotient of
`G_a` on `Z_a` with `SL₂(2)`, realizes the literal central quotient of
`Z_a` as its natural module using that same group equivalence, and recovers
the source omega-center formula.

The action-input and fixed-space modules assemble the two orientations of
the critical pair.  Their relative-index identities decide the source's
cardinality inequality.  If it points in the reverse direction, applying the
finite-module theorem there yields equality, which transports back to the
chosen orientation.  We then apply `sl2Two_module` to the chosen quotient
action.  Its fixed global subspace is identified with the literal
`vertexCenterPart`; a short equality transport preserves the returned natural
module action.  Finally `criticalPair_reconstruction` supplies the unbarred
Sylow and omega-center clauses.

All orientation and action-instance bookkeeping is private.  The sole public
theorem has exactly the audited standing hypotheses and four-clause source
conclusion, with one quotient-group equivalence shared by the group and
natural-module assertions.
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open AmalgamGraph

universe u

variable {M : Type u} [Group M] [Finite M]

private theorem naturalSL2TwoActionAlong_quotient_of_eq
    {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V]
    (C D : Subgroup V) [C.Normal] [D.Normal] (hCD : C = D)
    (hC : IsInvariant A V C) (hD : IsInvariant A V D)
    (eA : A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hNat :
      letI := quotientMulDistribMulAction (A := A) (G := V) C hC
      IsNaturalSL2TwoActionAlong (V ⧸ C) eA) :
    letI := quotientMulDistribMulAction (A := A) (G := V) D hD
    IsNaturalSL2TwoActionAlong (V ⧸ D) eA := by
  subst D
  simpa only using hNat

private theorem apply_sl2Two_module
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a))
    (hinputs : CriticalPairSL2Two.ActionInputs S a a' ha' hV)
    (hcard :
      let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
      let _ := vertexQuotientConjugationAction S a
      Nat.card ((vertexModule S a) ⧸
        FixedPoints.subgroup (oppositeImage S a a' ha')
          (vertexModule S a)) ≤ Nat.card (oppositeImage S a a' ha')) :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    ∃ Sbar : Sylow 2 (VertexActionQuotient S a),
      oppositeImage S a a' ha' ≤ (Sbar : Subgroup _) ∧
      (Nat.card ((vertexModule S a) ⧸
          FixedPoints.subgroup (oppositeImage S a a' ha')
            (vertexModule S a)) = Nat.card (oppositeImage S a a' ha') ∧
        oppositeImage S a a' ha' = (Sbar : Subgroup _) ∧
        (∃ ebarM : VertexActionQuotient S a ≃*
            Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
          let CbarM := FixedPoints.subgroup (VertexActionQuotient S a)
            (vertexModule S a)
          ∃ hCbarM : IsInvariant (VertexActionQuotient S a)
              (vertexModule S a) CbarM,
            letI := quotientMulDistribMulAction
              (A := VertexActionQuotient S a) (G := vertexModule S a)
              CbarM hCbarM
            IsNaturalSL2TwoActionAlong
              (vertexModule S a ⧸ CbarM) ebarM) ∧
        FixedPoints.subgroup (oppositeImage S a a' ha')
            (vertexModule S a) =
          commutatorAction (oppositeImage S a a' ha')
              (vertexModule S a) ⊔
            FixedPoints.subgroup (VertexActionQuotient S a)
              (vertexModule S a)) := by
  let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
  let _ := vertexQuotientConjugationAction S a
  obtain ⟨Sbar, hTbarSbar⟩ := hinputs.oppositeImage_isPGroup.exists_le_sylow
  refine ⟨Sbar, hTbarSbar, ?_⟩
  exact sl2Two_module Sbar (oppositeImage S a a' ha')
    (Stellmacher.SectionTwo.quotientConjugationAction_faithful
      (vertexSylow S a) (vertexActionQuotientMap S a)
      (QuotientGroup.mk'_surjective (vertexActionCentralizer S a))
      (QuotientGroup.ker_mk' (vertexActionCentralizer S a)))
    hinputs.quotientCore_eq_bot hinputs.quotientNestedSL2 hTbarSbar
    hinputs.oppositeImage_ne_bot hinputs.quotient_not_two
    hinputs.oppositeImage_quadratic hcard

private theorem criticalPair_cardinal_bound
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a))
    (hfixed : CriticalPairSL2Two.FixedSpaceData S a a' ha' hV)
    (ha : vertexZ S a ≤ stabilizer S a')
    (hV' : IsElementaryAbelian 2 (vertexModule S a'))
    (hinputs' : CriticalPairSL2Two.ActionInputs S a' a ha hV')
    (hfixed' : CriticalPairSL2Two.FixedSpaceData S a' a ha hV') :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    Nat.card ((vertexModule S a) ⧸
      FixedPoints.subgroup (oppositeImage S a a' ha')
        (vertexModule S a)) ≤ Nat.card (oppositeImage S a a' ha') := by
  let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
  let _ := vertexQuotientConjugationAction S a
  let _ : IsElementaryAbelian 2 (vertexModule S a') := hV'
  let _ := vertexQuotientConjugationAction S a'
  by_cases hcard : Nat.card ((vertexModule S a) ⧸
      FixedPoints.subgroup (oppositeImage S a a' ha')
        (vertexModule S a)) ≤ Nat.card (oppositeImage S a a' ha')
  · exact hcard
  · have hreverseCard :
        let _ : IsElementaryAbelian 2 (vertexModule S a') := hV'
        let _ := vertexQuotientConjugationAction S a'
        Nat.card ((vertexModule S a') ⧸
          FixedPoints.subgroup (oppositeImage S a' a ha)
            (vertexModule S a')) ≤ Nat.card (oppositeImage S a' a ha) := by
      dsimp only
      rw [hfixed'.fixedQuotient_card, hfixed'.oppositeImage_card]
      have hlt : Nat.card (oppositeImage S a a' ha') <
          Nat.card ((vertexModule S a) ⧸
            FixedPoints.subgroup (oppositeImage S a a' ha')
              (vertexModule S a)) := Nat.lt_of_not_ge hcard
      rw [hfixed.oppositeImage_card, hfixed.fixedQuotient_card] at hlt
      exact hlt.le
    obtain ⟨_, _, hmodule'⟩ :=
      apply_sl2Two_module S a' a ha hV' hinputs' hreverseCard
    have heq : Nat.card ((vertexModule S a) ⧸
          FixedPoints.subgroup (oppositeImage S a a' ha')
            (vertexModule S a)) = Nat.card (oppositeImage S a a' ha') := by
      calc
        Nat.card ((vertexModule S a) ⧸
            FixedPoints.subgroup (oppositeImage S a a' ha')
              (vertexModule S a)) =
            (vertexZ S a ⊓ vertexTwoCore S a').relIndex (vertexZ S a) :=
          hfixed.fixedQuotient_card
        _ = Nat.card (oppositeImage S a' a ha) :=
          hfixed'.oppositeImage_card.symm
        _ = Nat.card ((vertexModule S a') ⧸
            FixedPoints.subgroup (oppositeImage S a' a ha)
              (vertexModule S a')) := hmodule'.1.symm
        _ = (vertexZ S a' ⊓ vertexTwoCore S a).relIndex
            (vertexZ S a') := hfixed'.fixedQuotient_card
        _ = Nat.card (oppositeImage S a a' ha') :=
          hfixed.oppositeImage_card.symm
    exact heq.le

/-- Stellmacher, *Pushing up* (1986), Lemma (2.2), specialized to the
standing `p = 2`, `n = 1` hypotheses. -/
public theorem criticalPair_sl2Two
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' : Vertex S) (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S) :
    ∃ hV : IsElementaryAbelian 2 (vertexModule S a),
      ∃ ha' : vertexZ S a' ≤ stabilizer S a,
        CriticalPairSL2Two.Conclusion S a a' ha' hV := by
  obtain ⟨hV, ha', hinputs⟩ :=
    criticalPair_actionInputs S T hTS hP hSne hA a a' hcrit hb
  obtain ⟨hV', ha, hinputs'⟩ :=
    criticalPair_actionInputs S T hTS hP hSne hA a' a
      hinputs.critical.reverse_critical hb
  have hfixed := criticalPair_fixedSpaceData S a a' ha' hV hinputs
  have hfixed' := criticalPair_fixedSpaceData S a' a ha hV' hinputs'
  have hcard := criticalPair_cardinal_bound S a a' ha' hV hfixed
    ha hV' hinputs' hfixed'
  obtain ⟨Sbar, _, hmodule⟩ :=
    apply_sl2Two_module S a a' ha' hV hinputs hcard
  obtain ⟨_, hTbar, hsl2nat, hdecomp⟩ := hmodule
  obtain ⟨hSylow, hOmega⟩ :=
    criticalPair_reconstruction S a a' ha' hV hinputs hfixed Sbar
      hTbar hdecomp
  let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
  let _ := vertexQuotientConjugationAction S a
  have hsl2nat' :
      ∃ ebarG : VertexActionQuotient S a ≃*
          Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
        ∃ hC : IsInvariant (VertexActionQuotient S a) (vertexModule S a)
            (vertexCenterPart S a),
          letI := quotientMulDistribMulAction
            (A := VertexActionQuotient S a) (G := vertexModule S a)
            (vertexCenterPart S a) hC
          IsNaturalSL2TwoActionAlong
            (vertexModule S a ⧸ vertexCenterPart S a) ebarG := by
    obtain ⟨ebarG, hCF, hnatural⟩ := hsl2nat
    let F := FixedPoints.subgroup (VertexActionQuotient S a)
      (vertexModule S a)
    have hFC : F = vertexCenterPart S a := by
      simpa [F] using hfixed.globalFixed_eq_centerPart
    have hCC : IsInvariant (VertexActionQuotient S a) (vertexModule S a)
        (vertexCenterPart S a) := by
      rw [← hFC]
      exact hCF
    exact ⟨ebarG, hCC,
      naturalSL2TwoActionAlong_quotient_of_eq F (vertexCenterPart S a)
        hFC hCF hCC ebarG hnatural⟩
  exact ⟨hV, ha', ⟨hSylow, hsl2nat', hOmega⟩⟩

end Stellmacher.PushingUp
