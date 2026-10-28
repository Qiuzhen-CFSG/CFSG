module
public import CFSG.Quasithin.Chapter10.SourceA5PointActionMarking
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.FullMovedEquivalence

/-!
# Original coordinates for the classified point actor

Once the A7 cohomology argument eliminates the component-fixed space,
the original reduced orbit module is its B.5.1 central quotient. The actor
on the original module is the literal image of I in H/C_H(VI); the classified
actor is its subgroup inside the offender group. The canonical subgroup
equivalence and quotient projection intertwine these two actual actions.
Source: Aschbacher–Smith 10.2.9, printed pp.751–753.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Coordinates preserve the literal actor inclusion and original module. -/
def source_a5_point_action_coordinates
    {v : G} (I : Subgroup G)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := I ⊔ P
    let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I).subgroupOf H
    letI := hr.normal; letI := hr.elementary
    let A := (I.subgroupOf H).map (actionMk U)
    let N := offenderSubgroup (action U)
    let C := A.subgroupOf N
    ∀ _hAN : A ≤ N,
    ∀ s : MovedSection ((action U).comp N.subtype) C,
    moved ((action U).comp N.subtype) C = ⊤ →
    fixedSpace ((action U).comp N.subtype) C = ⊥ →
    ActionEquiv ((action U).comp A.subtype)
      (s.central.quotientRepresentation.comp C.subtype) := by
  dsimp only
  let P := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ P
  let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (P : Set G)) I).subgroupOf H
  let := hr.normal
  let := hr.elementary
  let A := (I.subgroupOf H).map (actionMk U)
  let N := offenderSubgroup (action U)
  let C := A.subgroupOf N
  intro hAN s hm hc
  let E : C ≃* A := subgroupOfEquivOfLe hAN
  refine ⟨E.symm, s.fullProjectionEquiv hm hc, ?_⟩
  intro a z
  exact s.fullProjection_intertwines hm (E.symm a : N) z

end CFSG.Quasithin.Chapter10
