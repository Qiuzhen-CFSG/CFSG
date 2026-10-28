module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelFusionSylow
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionControl

/-!
# Fusion control on the literal eight-field component

The original generated base realizes returning central-class fusion. Its
full endpoint join has a unique coset fixed by the original central involution
and controls all fusion on the actual ambient Sylow. Full ambient centralizers
of returning central involutions in the base lie in that endpoint join.
The proved K join T=K identity identifies the literal component base.

The marked inclusion-amalgam realization remains explicit, with independent
producer qt-e-1427-eight-amalgam-recognition. The second involution centralizer,
ambient generation, recognition and the Borel contradiction remain with
qt-e-14315-eight-borel-exclusion; none is assumed or asserted here.
Source: Aschbacher--Smith F.4.35, F.4.42, 14.2.18--19 and 14.3.15,
printed pp.292,295,987,994.
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


/-- The original component-generated base realizes all returning central-class fusion. -/
theorem source_eight_marked_generated_fusion_control
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T:Subgroup G)))
    (x : (K ⊔ EightLargeParabolic.secondParabolic T M Mc K : Subgroup G))
    {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1) (hconj : IsConj z (x:G)) :
    ∃ a : (K ⊔ EightLargeParabolic.secondParabolic T M Mc K : Subgroup G),
      (a:G)*(x:G)*(a:G)⁻¹=z := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have hx : (x:G)∈(K ⊔ (T:Subgroup G)) ⊔
      EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T:Subgroup G)) := by
    simpa only [hjoin] using x.property
  obtain ⟨a,ha⟩ := EightLargeParabolic.source_generated_fusion_control
    hG hempty hM hu hmany hcard e hH r ⟨x,hx⟩ hz hz1 hconj
  have haK : (a:G)∈K ⊔ EightLargeParabolic.secondParabolic T M Mc K := by
    simpa only [hjoin] using a.property
  exact ⟨⟨a,haK⟩,ha⟩

/-- The original central involution has a unique fixed coset of the full
endpoint join; the odd cubic supplement is retained. -/
theorem source_eight_marked_central_unique_fixed
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T:Subgroup G)))
    {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1) :
    ∃! q : G ⧸ (Mc ⊔ M), z • q=q := by
  exact EightLargeParabolic.source_central_unique_fixed hG hempty hM hu hmany hcard e
    (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1 r hz hz1

/-- All ambient fusion on the literal source Sylow is realized inside Mc join M. -/
theorem source_eight_marked_full_sylow_fusion
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T:Subgroup G)))
    {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    {x y : G} (hx : x∈(T:Subgroup G)) (hy : y∈(T:Subgroup G))
    (hxy : IsConj x y) : ∃ a∈Mc ⊔ M, a*x*a⁻¹=y := by
  exact EightLargeParabolic.source_sylow_full_fusion_control hG hempty hM hu hmany hcard e
    (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1 r hz hz1 hx hy hxy

/-- The generated component base retains the full ambient centralizers of
its returning central class inside the original full endpoint join. -/
theorem source_eight_marked_generated_long_centralizer
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T:Subgroup G)))
    (x : (K ⊔ EightLargeParabolic.secondParabolic T M Mc K : Subgroup G))
    {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1) (hconj : IsConj z (x:G)) :
    centralizer ({(x:G)}:Set G)≤Mc ⊔ M := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hx : (x:G)∈(K ⊔ (T:Subgroup G)) ⊔
      EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T:Subgroup G)) := by
    simpa only [hjoin] using x.property
  exact EightLargeParabolic.source_generated_long_centralizer_le hG hempty hM hu hmany hcard e
    (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1 r ⟨x,hx⟩ hz hz1 hconj

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
