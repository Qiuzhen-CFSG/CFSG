module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelResidual
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.Component

/-!
# The actual eight-row component is normal in the partner centralizer

Apply the completed containing-component comparison to H = K join T.
The checked embedded O² identity and marked parabolic perfectness identify
H with the original ComponentLift K. Consequently K is a normal C-component
of Mc, its full ambient normalizer is Mc, and Mc = K join (M intersect Mc).
No Sylow containment or component-normality premise is added.

Source: Aschbacher--Smith 14.2.18 and its eight-field application in 14.3.15,
printed pp.987,994. The independent marked realization is still explicit.
The cubic extension, ambient recognition and final Borel exclusion remain
with qt-e-14315-eight-borel-exclusion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
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


/-- Normal component identification on the literal ComponentLift/EightImageRow. -/
theorem source_eight_marked_normal_component
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    (K.subgroupOf Mc).IsCComponent ∧ (K.subgroupOf Mc).Normal := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  simpa only [hjoin] using EightLargeParabolic.source_first_normal_component
    hG hempty hM hu hmany hcard e hH r

/-- The normalizer and supplement are the original ambient subgroups. -/
theorem source_eight_marked_normalizer_and_factorization
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    normalizer (K : Set G) = Mc ∧ Mc = K ⊔ (M ⊓ Mc) := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  constructor
  · simpa only [hjoin] using EightLargeParabolic.source_first_normalizer_eq
      hG hempty hM hu hmany hcard e hH r
  · simpa only [hjoin] using EightLargeParabolic.source_partner_factorization
      hG hempty hM hu hmany hcard e hH r

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
