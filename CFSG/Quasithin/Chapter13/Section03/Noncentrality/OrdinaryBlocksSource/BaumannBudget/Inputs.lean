module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryBlocksSource.Contracts

/-!
# Exact remaining Baumann source interfaces

The diagonal A₅ argument must identify the Baumann subgroup of the original
point radical with that of O₂(KT). The earlier natural-six theorem must turn
escape of this same Baumann normalizer into the original A₆ block. These are
proof targets, not established book theorems. The source assembly retains
both obligations until their producers are supplied.

Source: Aschbacher--Smith 13.2.2(7), 13.2.4(1), 13.3.10(2) and13.3.14,
printed pp.877--879,887--888,893.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)

/-- The literal selected-component Baumann identity, before block recognition. -/
def OrdinaryBaumannIdentitySource : Prop :=
  ∀ K : Subgroup H, K.IsCComponent →
      IsComponent (Star H) (K.map (QuotientGroup.mk' (pCore 2 H))) →
      ⁅K.map (QuotientGroup.mk' (pCore 2 H)),
        (star H (sourceOne L T P) (ordinary_point_residual_le_point d)).pCoreIn 2⁆ ≠ ⊥ →
      (sourceOne L T P).subgroupOf H ≤ normalizer (K : Set H) →
      ⁅K,(sourceOne L T P).subgroupOf H⁆ = K → IsQuasisimple (K ⧸ pCore 2 K) →
      ⁅conjugateSpanBy U H,K.map H.subtype⁆ ≠ ⊥ →
      K.map H.subtype ∈ MainForward.faithfulLocalComponents T →
      (¬ sourceOne L T P ≤ K.map H.subtype) →
      Chapter6.Source.IsConjugationModel (K.map H.subtype)
        (Diagonal.movedModule (K.map H.subtype) (sourceOne L T P) T)
        Chapter6.Source.a5Module →
      ChapterB.baumann ((sourceOne L T P ⊔ (T : Subgroup G)).pCoreIn 2) =
        ChapterB.baumann ((K.map H.subtype ⊔ (T : Subgroup G)).pCoreIn 2)

/-- The original natural-six block alternative, retaining the precise R₁.
The native C.1.37 theorem is the earlier source for this target. -/
def OrdinaryBaumannBlockAlternative (_d : NaturalSetup T L V P E U M H) : Prop :=
  ¬ normalizer (ChapterB.baumann
    ((sourceOne L T P ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M →
    ChapterC.IsAlternatingBlock (L.subgroupOf (L ⊔ (T : Subgroup G))) 6

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
