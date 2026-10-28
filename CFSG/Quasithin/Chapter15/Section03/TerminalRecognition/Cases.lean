module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Reductions
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Survivors

/-!
# Terminal case reductions for Theorem 15.3.1

From the genuine 15.3.66–68 configuration and the full F.6.18/B.5.6
witnesses, the actual image of X = J(G₀) has the eight source possibilities.
The S₃ branch identifies X_E with the embedded two-residual of X and proves
that Z and F = ⟨Z^{Y_F}⟩ centralize X. It remains an explicit alternative
for the parent's normalizer contradiction.

In the other branch the intersection proves O²(X) = O²(G₀). Consequently
Y_F lies in X and V₀ = [V₀,X]. The marked local-core and module obstructions
leave G₀/O₂(G₀) isomorphic to S₆, S₇ or G₂(2), or carrying the source Ŝ₆
covering and sign-action witness. The quotient maps, local embeddings and
original conjugation action are unchanged. In particular, the proved
residual can be passed to `SourceInput.toActionInput` for the independent
exceptional-action recognition, whose concrete cover comparison is separate.

These are conditional case reductions, not a proof of either universal
classifier or of Theorem 15.3.1. The parent constructs the source input,
discharges the classifiers, eliminates the S₃ alternative, and assembles
the exceptional-action and normalizer contradictions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed p.1155, PDF p.1172.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison

universe u

namespace Cases
variable {H : Type u} [Group H] [Finite H] {V : Subgroup H}

/-- The S₃ outcome, retained for the parent's ambient normalizer argument.
All residuals and centralizers are taken in the actual source groups. -/
structure SymmetricThreeConclusion (d : Intersection.SourceInput V) (Z : Subgroup H) : Prop where
  image : Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))
  residual : d.XE = (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype
  center_centralizes : Z ≤ centralizer (thompsonGroup H : Set H)
  span_centralizes : conjugateSpanBy Z d.YF ≤ centralizer (thompsonGroup H : Set H)
  singular_centralizes : d.F ≤ centralizer (thompsonGroup H : Set H)

/-- The non-S₃ output of the source intersection and marked exclusions.
The fixed subspace is V inside V₀, not the trivial group image of V modulo Q₀.
`d.toActionInput residual` supplies the unchanged later recognition input. -/
structure NonS3Conclusion [IsElementaryAbelian 2 (moduleClosure V)]
    (d : Intersection.SourceInput V) : Prop where
  image : Intersection.NonS3ImageAlternative ((thompsonGroup H).map coreProjection)
  quotient : SurvivingQuotientAlternative (coreQuotient H)
  residual : (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H
  first_le : d.YF ≤ thompsonGroup H
  closure_commutator : moduleClosure V = ⁅moduleClosure V, thompsonGroup H⁆
  local_core_strict : (d.YF.map coreProjection).pCoreIn 2 < (d.G1.map coreProjection).pCoreIn 2
  vector_fixed : planeSubspace V V ≤
    fixedSpace (quotientAction V d.centralizer_isTwoGroup d.core_centralizes)
      ((d.YF.map coreProjection).pCoreIn 2)
  vector_finrank : Module.finrank (ZMod 2) (planeSubspace V V) = 4

end Cases

namespace Intersection.SourceInput
variable {H : Type u} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The non-S₃ case on the original marked configuration. The classification
intersection supplies the residual equality; the genuine local and module
exclusions supply the four surviving quotients without an extra model premise. -/
theorem source_nonS3_cases_of_classifications
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃*
      Equiv.Perm (Fin 3))) : Cases.NonS3Conclusion d := by
  obtain ⟨hX, _, hres⟩ := d.source_nonS3_intersection_of_classifications hF hB hnot
  obtain ⟨hY, hV⟩ := d.source_moduleClosure_commutator_of_classifications hF hB hnot
  exact ⟨hX, d.source_surviving_quotient_of_classifications hF hB hnot,
    hres, hY, hV, d.local_core_strict, d.vector_fixed, (d.toActionInput hres).vector_finrank⟩

/-- The conditional terminal source split. The additional E,Z premises
are the earlier centralization and conjugate-span facts used only for S₃;
no branch, residual equality or terminal model is assumed. -/
theorem source_terminal_cases_of_classifications
    (E Z : Subgroup H) (hZE : Z ≤ E)
    (hXE : d.XE ≤ centralizer (E : Set H))
    (hZT : Z ≤ centralizer (d.T : Set H))
    (hFspan : d.F = conjugateSpanBy Z d.YF)
    (hF : FSource.Alternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.Alternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction) :
    Cases.SymmetricThreeConclusion d Z ∨ Cases.NonS3Conclusion d := by
  by_cases hs : Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))
  · obtain ⟨hres, hZ, hspan⟩ := symmetricThree_branch d.T d.XE E Z d.YF
      d.second_commutator d.second_escape d.second_perfect
      ((d.second_local.symm ▸ le_sup_right).trans d.second_normalized)
      hZE hXE hZT hs.some
    exact Or.inl ⟨hs, hres, hZ, hspan, hFspan.symm ▸ hspan⟩
  · exact Or.inr (d.source_nonS3_cases_of_classifications hF hB hs)

/-- Specialize both universal source classifiers to the genuine local
configuration and offender action, retaining the S₃ branch for its owner.
The classifier proofs and the source configuration remain with their source owners. -/
theorem source_terminal_cases_of_full_classifications {K : GroupClass.{u}}
    (hH : IsSQTK K H)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : SourceFFClassificationInput.{u,u} K)
    (E Z : Subgroup H) (hZE : Z ≤ E)
    (hXE : d.XE ≤ centralizer (E : Set H))
    (hZT : Z ≤ centralizer (d.T : Set H))
    (hFspan : d.F = conjugateSpanBy Z d.YF) :
    Cases.SymmetricThreeConclusion d Z ∨ Cases.NonS3Conclusion d :=
  d.source_terminal_cases_of_classifications E Z hZE hXE hZT hFspan
    (d.full_goldschmidt_alternative hH classificationF)
    (d.full_sourceFF_alternative hH classificationB)

/-- After the parent's S₃ contradiction, both universal source classifiers
give the four quotient possibilities and every residual, commutator and
fixed-subspace constraint needed by the later action recognition. -/
theorem source_nonS3_cases_of_full_classifications {K : GroupClass.{u}}
    (hH : IsSQTK K H)
    (classificationF : FSource.ClassificationInput K)
    (classificationB : SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃*
      Equiv.Perm (Fin 3))) : Cases.NonS3Conclusion d :=
  d.source_nonS3_cases_of_classifications
    (d.full_goldschmidt_alternative hH classificationF)
    (d.full_sourceFF_alternative hH classificationB) hnot

end Intersection.SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
