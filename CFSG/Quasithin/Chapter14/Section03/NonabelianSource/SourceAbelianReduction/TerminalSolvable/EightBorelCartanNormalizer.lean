module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelCartan
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.CartanNormalizer

/-!
# The actual Cartan normalizer in the original eight-field row

Apply the exact native centralizer and normalizer calculation to the literal
ComponentLift/EightImageRow. The same torus Q used by the actual order-six
endpoint pair has centralizer of order eight in the original T. Its normalizer
inside the original Mc intersection M is its centralizer and has order 56.
The proved endpoint equalities identify that whole overlap, including its odd
factor; no assumption T ≤ K is used.

These are local inputs for the outstanding matching native hexagon relation.
They do not assert ambient recognition or the Borel contradiction. The genuine
earlier MarkedTriality premise still retains both original commuting squares.
Source: Aschbacher--Smith F.4.15--17 and14.3.6,15, pp.281--283,991,994.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
include hG hempty hM hu hmany hcard e

/-- Exact local centralizers and normalizers of the same torus used by the
actual endpoint reflections, on the original source Sylow and overlap. -/
theorem source_eight_marked_cartan_normalizer
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    let c := EightLargeParabolic.markedCompletion r
    let Q := (ChapterF.SourceCompletion.TrialityTwo.Completion.borelTorus.map c.middle).map
      ((K ⊔ (T : Subgroup G)) ⊔ EightLargeParabolic.secondParabolic T M Mc
        (K ⊔ (T : Subgroup G))).subtype
    Nat.card Q = 7 ∧
      Nat.card ((T : Subgroup G) ⊓ centralizer (Q : Set G) : Subgroup G) = 8 ∧
      (T : Subgroup G) ⊓ normalizer (Q : Set G) =
        (T : Subgroup G) ⊓ centralizer (Q : Set G) ∧
      (Mc ⊓ M) ⊓ normalizer (Q : Set G) =
        (Mc ⊓ M) ⊓ centralizer (Q : Set G) ∧
      Nat.card ((Mc ⊓ M) ⊓ normalizer (Q : Set G) : Subgroup G) = 56 := by
  dsimp only
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have hp := EightLargeParabolic.source_endpoints_eq
    hG hempty hM hu hmany hcard e hH r
  have hQ : (ChapterF.SourceCompletion.TrialityTwo.Completion.borelTorus.map
      (EightLargeParabolic.markedCompletion r).middle).map
      ((K ⊔ (T : Subgroup G)) ⊔ EightLargeParabolic.secondParabolic T M Mc
        (K ⊔ (T : Subgroup G))).subtype = EightLargeParabolic.ambientTorus r :=
    map_map _ _ _
  have hI : Mc ⊓ M = (K ⊔ (T : Subgroup G)) ⊓
      EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T : Subgroup G)) :=
    congrArg₂ (fun A B : Subgroup G => A ⊓ B) hp.1 hp.2.symm
  rw [hQ]
  refine ⟨EightLargeParabolic.ambientTorus_card r,
    EightLargeParabolic.ambientTorus_sylow_centralizer_card r le_sup_right,
    EightLargeParabolic.ambientTorus_sylow_normalizer r le_sup_right,?_,?_⟩
  · rw [hI]
    exact EightLargeParabolic.ambientTorus_overlap_normalizer r
  · rw [hI]
    exact EightLargeParabolic.ambientTorus_overlap_normalizer_card r

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
