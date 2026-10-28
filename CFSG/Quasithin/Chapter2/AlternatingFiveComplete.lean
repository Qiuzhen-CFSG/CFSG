module

public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSingleSource

/-!
# Complete source exclusion for the single alternating-five block

The Chapter 2 forward dispatcher isolates one genuine source premise: a
minimal alternating-five block with trivial intersection between the selected
Sylow and its block centralizer.  The source argument for this branch is
already assembled in `AlternatingSingleSource`; this adapter exposes it in the
exact dependent form used by the Main Theorem dispatcher.

Source: Aschbacher--Smith 2.4.29, printed pp.545--546.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The trivial-centralizer alternating-five branch, in dispatcher form. -/
theorem single_alternating_five_exclusion_complete
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) :
    ∀ (N : Subgroup G) (d : MinimalBlockSetup N) (P : Sylow 2 G),
      IsMaximalTwoLocal N → (P : Subgroup G) ≤ N →
      (∀ J : Subgroup G, IsMaximalTwoLocal J → (P : Subgroup G) ≤ J → J = N) →
      (delta (Chapter1.He G) N).Nonempty →
      (d.S : Subgroup d.H).map d.H.subtype < (P : Subgroup G) →
      ¬ IsTheorem241Model G → d.L0 = d.block →
      IsAlternatingBlock (d.block.map d.H.subtype) 5 →
      (P : Subgroup G) ⊓
          centralizer (d.block.map d.H.subtype : Set G) = ⊥ → False := by
  intro N d P hN hPN hPu hdelta hSP hcounter hsingle hA hD
  exact d.single_alternating_source_false hG P hN hPN hPu hdelta hcounter hSP
    hsingle hA

end CFSG.Quasithin.Chapter2
