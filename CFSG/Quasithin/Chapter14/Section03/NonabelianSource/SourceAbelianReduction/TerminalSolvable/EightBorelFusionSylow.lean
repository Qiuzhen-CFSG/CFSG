module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelFusionOrbit
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionSylow

/-!
# Sylow and endpoint fusion on the literal eight-field component

Every ambient conjugate of the original central involution returning to the
chosen Sylow or either marked parabolic has a long-root model image. The
second endpoint supplies an actual conjugator into the literal component
core, with both endpoint equations and its quotient orbit bound retained.
The proved equality K join T = K identifies that core without assuming it.

The independent marked inclusion-amalgam realization remains explicit, owned
by qt-e-1427-eight-amalgam-recognition. Full fusion comparison, the second
involution centralizer, matching relation, ambient recognition and the Borel
contradiction remain with qt-e-14315-eight-borel-exclusion.
Source: Aschbacher--Smith F.4.30--35, pp.289--292; 14.2.18--19 and
14.3.15, pp.987,994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.EvenInvolutionGeometry
local notation "P" => binaryParameters 1 Nat.zero_lt_one
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

/-- Returning central involutions in the entire original Sylow have long-root
image in the literal ComponentLift/EightImageRow marking. -/
theorem source_eight_marked_sylow_fusion
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T:Subgroup G)))
    {x z : G} (hx : x∈(T:Subgroup G)) (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z x) :
    IsLongRootInvolution 1 Nat.zero_lt_one (r.left ⟨x,(show (T:Subgroup G)≤K ⊔ (T:Subgroup G) from le_sup_right) hx⟩).val := by
  exact EightLargeParabolic.source_sylow_fusion_isLongRoot hG hempty hM hu hmany hcard e
    (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1 r hx hz hz1 hconj

/-- The original second endpoint moves the returning Sylow involution into
the literal component core, retaining its model value and orbit bound. -/
theorem source_eight_marked_sylow_core_bound
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T:Subgroup G)))
    {x z : G} (hx : x∈(T:Subgroup G)) (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z x) :
    ∃ b : EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T:Subgroup G)),
      ∃ q : K.pCoreIn 2, ∃ v : radical P .arms,
        (q:G)=(b:G)*x*(b:G)⁻¹ ∧
        v.val=(r.left ⟨q,(show K≤K ⊔ (T:Subgroup G) from le_sup_left) (pCoreIn_le 2 K q.property)⟩).val ∧
        v.val=(r.right b).val*(r.left ⟨x,(show (T:Subgroup G)≤K ⊔ (T:Subgroup G) from le_sup_right) hx⟩).val*(r.right b).val⁻¹ ∧
        IsLongRootInvolution 1 Nat.zero_lt_one v.val ∧
        (ArmsOrbit.points (ArmsOrbit.point v)).ncard≤9 := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  obtain ⟨b,q,hq,hqm,hlong,hbound⟩ := EightLargeParabolic.source_sylow_fusion_core_bound
    hG hempty hM hu hmany hcard e hH r hx hz hz1 hconj
  have hqK : (q:G)∈K.pCoreIn 2 := by simpa only [hjoin] using q.property
  exact ⟨b,⟨q,hqK⟩,EightLargeParabolic.firstCoreEquiv r q,hq,
    EightLargeParabolic.firstCoreEquiv_val r q,hqm,hlong,hbound⟩

/-- Fusion of the central involution into either literal endpoint of the
component amalgam has a long-root image under that same endpoint map. -/
theorem source_eight_marked_endpoint_fusion
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T:Subgroup G)))
    {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1) :
    (∀ x : K, IsConj z (x:G) → IsLongRootInvolution 1 Nat.zero_lt_one
      (r.left ⟨x,(show K≤K ⊔ (T:Subgroup G) from le_sup_left) x.property⟩).val) ∧
    (∀ x : EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T:Subgroup G)),
      IsConj z (x:G) → IsLongRootInvolution 1 Nat.zero_lt_one (r.right x).val) := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact ⟨fun x hx => EightLargeParabolic.source_first_fusion_isLongRoot
      hG hempty hM hu hmany hcard e hH r ⟨x,(show K≤K ⊔ (T:Subgroup G) from le_sup_left) x.property⟩ hz hz1 hx,
    fun x hx => EightLargeParabolic.source_second_fusion_isLongRoot
      hG hempty hM hu hmany hcard e hH r x hz hz1 hx⟩
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
