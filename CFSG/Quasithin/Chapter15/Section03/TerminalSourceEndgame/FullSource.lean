module

public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.SourceControls
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.FullSource

/-!
# The terminal contradiction from the corrected F.6 alternatives

The corrected classification retains the ambient dihedral and both
square-field branches. The completed source intersection already reduces
all of them to the same S₃ or surviving-quotient alternatives. In the
second case the existing action recognizer and marked-plane theorem give
an A₅ quotient of the original definite-plane normalizer, contradicting
its containment in the solvable M. Thus no legacy thirteen-row classifier
or replacement local-model assertion is required in the terminal consumer.

Source: Aschbacher--Smith F.6.18 and the last paragraph of 15.3.1,
printed pp.309--310 and1155.
-/

public section
open Subgroup Atlas.Codes Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame
open TerminalRecognition TerminalRecognition.ExceptionalAction AbelianAmalgam
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {G₀ M V : Subgroup G}
  {d : NaturalOrthogonalAction M V}
  {a : Intersection.SourceInput (V.subgroupOf G₀)}

/-- The complete corrected source alternatives feed the existing action
recognition on the same offender module and definite plane. -/
theorem terminal_contradiction_of_source_classifications
    (g : EarlierGeometry d a) (h : EarlierControls g)
    {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.SourceClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hZE : centralInvolutions g.T ≤ g.E)
    (hFspan : a.F = conjugateSpanBy ((centralInvolutions g.T).subgroupOf G₀) a.YF) :
    False := by
  let _ := g.moduleClosure_elementary
  obtain ⟨hXE,hZT⟩ := g.seed_centralizers
  have hB := a.full_sourceFF_alternative hG₀ classificationB
  rcases a.source_terminal_cases_of_source_classifications hG₀ classificationF classificationB
      (g.E.subgroupOf G₀) ((centralInvolutions g.T).subgroupOf G₀)
      (fun _ hz => hZE hz) hXE hZT hFspan with hs | hn
  · exact symmetricThree_impossible g h.normalizer_escape_singular h.residual_escape hs
  · obtain ⟨c⟩ := (a.toActionInput hn.residual).nonempty_coordinates_of_surviving_source
      hn.quotient hB
    have hp := MarkedPlane.localPlane_isFullWeightScalarPlane c (g.configuration hn.first_le) 1
    obtain ⟨f,hf⟩ := c.exists_surjective_planeStabilizer (localPlane G₀ M V d 1) hp
    obtain ⟨q,hq⟩ := exists_surjective_planeNormalizer_to_A5 (V.subgroupOf G₀)
      a.centralizer_isTwoGroup a.core_centralizes (thompsonGroup G₀)
      (localPlane G₀ M V d 1) ((localPlane_le G₀ M V d 1).trans le_normalClosure) f hf
    let e := g.planeNormalizerEquiv 1
    let L := ambientThompson G₀ ⊓ normalizer (d.plane 1 : Set G)
    have hLM : L ≤ M := inf_le_right.trans h.definite_normalizer
    let _ := h.solvable
    let _ : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hLM) (inclusion_injective hLM)
    let _ : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
      (Group.isSolvable_of_surjective
        (show Function.Surjective (q.comp e.symm.toMonoidHom) from hq.comp e.symm.surjective))

/-- The same corrected terminal implication with the literal ambient
singular span supplied by the original source construction. -/
theorem terminal_contradiction_of_source_ambient_span
    (g : EarlierGeometry d a) (h : EarlierControls g)
    {K : GroupClass.{u}} (hG₀ : IsSQTK K G₀)
    (classificationF : FSource.SourceClassificationInput K)
    (classificationB : Intersection.SourceFFClassificationInput.{u,u} K)
    (hZE : centralInvolutions g.T ≤ g.E)
    (hspan : otherLine g.E g.s = conjugateSpanBy (centralInvolutions g.T)
      (otherLine (lineY (residualY M g.Mc) g.E) g.s)) : False :=
  terminal_contradiction_of_source_classifications g h hG₀ classificationF classificationB hZE
    (g.intrinsic_seed_span hZE hspan)

end CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame
