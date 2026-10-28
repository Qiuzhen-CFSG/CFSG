module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import Theory.GroupTheory.PGroup.Omega

/-!
# Intermediate interfaces for the high-three-rank branch

These are targets for the two successive arguments in B.5.7, not additional
assumptions of B.5.3 or previously proved source theorems. The cover argument
must construct `NoncentralContext`, unless it proves the central Fitting case.
The module argument must then construct `CubicCentralizers` on the original
component and the original three-core. Neither record asserts an outer shape
or any splitting of the representation.

In particular the cover remains an actual finite SQTK group with its actual
surjection. Its three-core, its component, their centers and their images are
not replaced by group-family labels. The `omega` equality is in that cover.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.2,
printed pp.103–104, and the proof of B.5.7, printed pp.105–106.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank
universe u

/-- The proved nilpotent-presentation portion of B.5.2, before lifting components. -/
structure PreparedCover (K : GroupClass.{u}) (G : Type u) [Group G] where
  Cover : Type u
  [coverGroup : Group Cover]
  [coverFinite : Finite Cover]
  projection : Cover →* G
  surjective : Function.Surjective projection
  sqtk : IsSQTK K Cover
  fitting_nilpotent : Group.IsNilpotent ((fittingSubgroup G).comap projection)
  kernel_nilpotent : Group.IsNilpotent projection.ker
  kernel_odd : Odd (Nat.card projection.ker)

attribute [instance] PreparedCover.coverGroup PreparedCover.coverFinite

/-- Target of the cover and centralizer argument in the noncentral branch.
All subgroups and all maps are in the original finite quotient presentation. -/
structure NoncentralContext (K : GroupClass.{u}) (G : Type u) [Group G]
    (L : Subgroup G) where
  cover : PreparedCover K G
  lift : Subgroup cover.Cover
  component : IsComponent cover.Cover lift
  component_image : lift.map cover.projection = L
  lift_rank : 1 < primeRank 3 lift
  lift_layer : componentLayer cover.Cover = lift
  layer : componentLayer G = L
  normal : L.Normal
  component_sqtk : IsSQTK K L
  fitting : generalizedFitting G = (L ⊔ pCore 3 G) ⊔ center G
  noncentral : ¬ pCore 3 G ≤ center G
  odd_centralizer : Odd (Nat.card (centralizer (L : Set G)))
  cyclic_threeCore : IsCyclic (pCore 3 cover.Cover)
  omega : (omega₁ (pCore 3 cover.Cover) (p := 3)).map (pCore 3 cover.Cover).subtype =
    (center lift).map lift.subtype

/-- Target of the offender/module calculation on the same `L` and `O₃(G)`.
The two model identifications are actual multiplicative equivalences. -/
structure CubicCentralizers (G : Type u) [Group G] (L : Subgroup G) where
  componentEquiv : L ≃* alternatingGroup (Fin 6)
  threeCoreEquiv : pCore 3 G ≃* Multiplicative (ZMod 3)
  component_centralizer : centralizer (L : Set G) = pCore 3 G
  threeCore_centralizer : centralizer (pCore 3 G : Set G) = L ⊔ pCore 3 G

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank
