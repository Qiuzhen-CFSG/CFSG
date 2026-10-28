module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Reductions
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Actors
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.Models
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.ComponentRows
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceClassifications
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceComponentRows
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SourceLowRows

/-!
# Conditional terminal classification intersection

The source input precedes the intersection: it does not assume a Thompson
residual identity or any classification alternative. Both classifications
are applied to their actual groups, with the quotient map, local embeddings
and original conjugation representation preserved.

The checked reductions show that the Thompson image is nonabelian, lies
in the offender actor, and equals that actor in the S₃ and quasisimple
actor branches. When the ambient generalized Fitting subgroup is
quasisimple it lies in the Thompson image. A two-group quotient over it
then yields the required equality of embedded residuals in H. In particular
this finishes the residual calculation in the full-component rows. The
strict local-core inequality also excludes the first F.6.18 row.

The corrected source row comparisons assemble into the eight-image
alternative, with the ambient alternatives and embedded residual equality
in the non-S₃ branch. The action witness uses vector dimension two for
the F₄ projective line and retains all six B.5.1 clauses. The separate outer
A₆–C₃ branch needs only its actual group configuration. The application
proves `Y_F ≤ J(H)` and `V₀ = [V₀,J(H)]` on the original module closure,
discharging the residual premise of the later action recognition.

The `source_*` theorems provide the conditional source intersection;
the earlier `legacy_*` interfaces remain available separately. The final
application proves classification applicability from `SourceInput` and
the SQTK hypothesis, leaving only the universal source classifiers explicit.
Their proofs, the marked exclusions and the exceptional F₄/field-involution
comparison remain with their source owners. In particular the hatted
outputs retain genuine covering witnesses, and the full B-side action
remains on the original offender actor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final proof
of 15.3.1, printed p.1155; F.6.18, pp.309–310; B.5.1/B.5.6, pp.99–105.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

universe u

namespace SourceInput
variable {H : Type u} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The conditional source intersection on the literal image of J(H).
The full F.6.18 witness may use either local labeling; the full corrected
B.5.6 witness acts on the original module. No equality of the Thompson,
offender and ambient groups is assumed. -/
theorem source_intersection_of_classifications
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) ∨
      (NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
        AmbientAlternative (coreQuotient H) ∧
        (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype =
          pResidual 2 H) := by
  by_cases hL : IsQuasisimple (generalizedFitting (coreQuotient H))
  · exact Or.inr (d.source_component_intersection_of_classifications hL hF hB)
  · exact Or.inl (d.source_thompson_symmetricThree_of_nonquasisimple hF hB hL)

/-- After the separate S₃ exclusion, the source comparison gives the
ambient models needed by the marked exclusions and the literal residual
identity in H. The hatted cases retain their actual covering witnesses. -/
theorem source_nonS3_intersection_of_classifications
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃*
      Equiv.Perm (Fin 3))) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype =
        pResidual 2 H := by
  rcases d.source_intersection_of_classifications hF hB with h | h
  · exact (hnot h).elim
  · exact h

/-- The source intersection discharges the residual premise of the later
action input, giving both containment of Y_F and commutator generation on
the same conjugate-span module, with all local markings preserved. -/
theorem source_moduleClosure_commutator_of_classifications
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃*
      Equiv.Perm (Fin 3))) :
    d.YF ≤ thompsonGroup H ∧
      moduleClosure V = ⁅moduleClosure V, thompsonGroup H⁆ := by
  obtain ⟨_, _, hres⟩ := d.source_nonS3_intersection_of_classifications hF hB hnot
  exact ⟨(d.toActionInput hres).thompson_contains,
    (d.toActionInput hres).closure_commutator⟩

include d in
/-- Application of the universal source inputs to H = G₀. The genuine
15.3.66–68 data supplies the local quotient configuration and every B.5.3
applicability premise on the offender actor. Proving the universal inputs
remains with the source owners; no terminal model or residual is an input. -/
theorem source_intersection_of_full_classifications {K : GroupClass.{u}}
    (hH : IsSQTK K H)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : SourceFFClassificationInput.{u,u} K) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) ∨
      (NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
        AmbientAlternative (coreQuotient H) ∧
        (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype =
          pResidual 2 H) :=
  d.source_intersection_of_classifications
    (d.full_goldschmidt_alternative hH classificationF)
    (d.full_sourceFF_alternative hH classificationB)

/-- Exhaustive intersection of the existing conditional row comparisons.
The B-side premise is the legacy full-action contract, not the corrected
source classification. All group identifications and covers are actual. -/
theorem legacy_intersection_of_classifications
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : FFAlternatives.SourceAlternative d.offenderAction) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) ∨
      (NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
        AmbientAlternative (coreQuotient H) ∧
        (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype =
          pResidual 2 H) := by
  by_cases hL : IsQuasisimple (generalizedFitting (coreQuotient H))
  · exact Or.inr (d.component_intersection_of_classifications hL hF hB)
  · exact Or.inl (d.thompson_symmetricThree_of_nonquasisimple hF hB hL)

/-- After the separate S₃ exclusion, the existing conditional comparison
supplies the ambient alternatives and the embedded two-residual identity. -/
theorem legacy_nonS3_intersection_of_classifications
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : FFAlternatives.SourceAlternative d.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃*
      Equiv.Perm (Fin 3))) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype =
        pResidual 2 H := by
  rcases d.legacy_intersection_of_classifications hF hB with h | h
  · exact (hnot h).elim
  · exact h

/-- Consumer application on the literal `V₀ = moduleClosure V`: the
derived residual identity discharges the later action input's residual
premise and gives the source commutator generation, without changing the
module, either local embedding, or the conjugation action. -/
theorem legacy_moduleClosure_commutator_of_classifications
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : FFAlternatives.SourceAlternative d.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃*
      Equiv.Perm (Fin 3))) :
    d.YF ≤ thompsonGroup H ∧
      moduleClosure V = ⁅moduleClosure V, thompsonGroup H⁆ := by
  obtain ⟨_, _, hres⟩ := d.legacy_nonS3_intersection_of_classifications hF hB hnot
  exact ⟨(d.toActionInput hres).thompson_contains,
    (d.toActionInput hres).closure_commutator⟩

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
