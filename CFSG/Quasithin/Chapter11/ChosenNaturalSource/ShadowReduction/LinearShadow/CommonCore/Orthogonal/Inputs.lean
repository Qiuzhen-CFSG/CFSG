module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalCoordinates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic

/-!
# The source state before the odd-degree argument

This is the explicit contract between the preceding common-core construction
and the paragraph beginning “Assume n is even”. The original chosen module,
flag, outside subgroup and conjugator are retained. In particular the two
natural markings have independent fields, and the field-four obstruction has
already been discharged in the equalities O₂(L) = V = C_L(V).

Every field below belongs to 11.3.7 or the preceding two paragraphs on p.774.
This record asserts no existence theorem and contains none of the conclusions
of the odd-degree, relative-component or orthogonal-recognition arguments.
Its producers are the common-action and common-identification tasks; their
parent must construct it before using the conditional orthogonal argument.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
printed pp.773--774. The L₂ sections in the later action calculation are
V₂ and P/V₂; V is not a subgroup of P.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 m)) (H X A : Subgroup G) (h : G)

/-- Earlier source conclusions only, before the odd-degree paragraph.
`A` denotes the book's odd Hall group D; the chosen module is named `D`.
The post-11.3.7 Sylow assertion uses the original V, reflecting V = A
in the book's separate conjugate-seed notation. -/
structure OrthogonalInput where
  source : Hypothesis1131At D S ((Coordinates.sl3 m).binarySubspace (f.space 0)) H
  preceding : Preceding1133 D S ((Coordinates.sl3 m).binarySubspace (f.space 0)) H
  counterexample : ¬ Proposition1132At D S ((Coordinates.sl3 m).binarySubspace (f.space 0)) H
  unique_flag : f.IsUnique
  cartan : IsCartan T L X
  hall_le : A ≤ H ⊓ normalizer (L : Set G)
  hall : IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G)))
  oddCartan_le : oddCartanPart A ≤ X
  residual_component : ((outsideResidual H).subgroupOf H).IsCComponent
  closure_le_sylow : omegaClosure T H ≤ (T : Subgroup G)
  closure_natural : NaturalQuotientMarking T H S.field
  omega_fixed : omegaCenter T ⊓ centralizer (L : Set G) = ⊥
  seed_fixed : V ⊓ centralizer (L : Set G) = ⊥
  closure_fixed : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥
  seed_star_sylow : ∃ R : Sylow 2 (residualStar T H),
    (R : Subgroup (residualStar T H)).map (residualStar T H).subtype =
      (V.subgroupOf H).map (starProjection T H)
  line_moved : ⁅f.Vi 0, oddCartanPart A⁆ = f.Vi 0
  line_le_closure : f.Vi 0 ≤ omegaClosure T H
  conjugator_mem : h ∈ H
  conjugator_outside : h ∉ normalizer (L : Set G)
  pair_normal : ((pairGroup V h).subgroupOf H).Normal
  pair_residual : outsideResidual (pairGroup V h) = outsideResidual H
  conjugates_disjoint : V ⊓ V.map (MulAut.conj h).toMonoidHom = ⊥
  pair_core : (pairGroup V h).pCoreIn 2 = pairCore V H h
  residual_core : (outsideResidual H).pCoreIn 2 = pairCore V H h
  local_core : (f.Li 1).pCoreIn 2 = pairCore V H h
  axis_eq_plane : axis V H = f.Vi 1
  intersection_eq_plane : pairCore V H h ⊓ V = f.Vi 1
  block : ChapterC.IsSL3EvenBlock L S.field.degree
  seed_core : L.pCoreIn 2 = V
  seed_centralizer : L ⊓ centralizer (V : Set G) = V
  pair_field : BinaryField
  pair_degree : pair_field.degree = S.field.degree
  pair_natural : PairNaturalMarking V H h pair_field
  pair_multiplicity : pair_natural.multiplicity = 2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
