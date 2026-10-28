module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.Reductions
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Cover
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.Extension
public import Theory.SpecificGroups.SymplecticFour.InvolutionTypes

/-!
# The remaining concrete symplectic actor in source 11.2.4

This is an output specification for the reciprocal-action and transvection
exclusion argument, not an additional hypothesis of the source theorem.
The homomorphism acts on the entire original chosen module through its
actual central cover. Agreement only on the natural quotient would not
justify the nonsplit-cover root calculation. A symplectic basis identifies
the original point and plane, and the actual image lies in the corresponding
plane radical, has order q², and contains no rank-one involutions.

Constructing this data and proving its root-commutator consequence are separate
obligations. Neither a commutator identity nor a complement to C_V(L) is a
field of this specification. Source: Aschbacher--Smith, 11.2.4, printed p.770.
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

open Theory.SpecificGroups.SymplecticFour

/-- Concrete output still to be constructed in the strict-commutator branch.
The action equation retains the central kernel of the original module. -/
structure InnerPlaneActor
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m)) (A : Subgroup G) where
  hom : A →* Sp S.field.Carrier
  basis : Sp S.field.Carrier
  point : f.space 0 = (Theory.SpecificGroups.SymplecticFour.point S.field.Carrier).map
    (symplecticNatural 2 basis)
  plane : f.space 1 = (Theory.SpecificGroups.SymplecticFour.plane S.field.Carrier).map
    (symplecticNatural 2 basis)
  action : ∀ (a : A) (v : D.space),
    (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (hom a) v)) : G) =
      (a : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (a : G)⁻¹
  range_le : hom.range ≤
    (Plane.radical.map planeLocal.subtype).map (MulAut.conj basis).toMonoidHom
  card_range : Nat.card hom.range = 2 ^ (2 * S.field.degree)
  no_transvections : ∀ a ∈ hom.range, ¬ InvolutionTypes.IsB1 a

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane
