module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelFusionSeparation
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FusionOrbit

/-!
# Returning-core fusion on the literal eight-field component

Apply the general core-fusion theorem to the original ComponentLift and
EightImageRow. The proved equality K join T = K transports the actual core;
the image is the value of the same first endpoint marking. Every returning
central involution has long-root image and quotient orbit of size at most nine.
The entire short-root quotient orbit, including its central lifts, is excluded.

The marked inclusion-amalgam realization remains the independent earlier input
owned by qt-e-1427-eight-amalgam-recognition. Full Sylow fusion, the second
involution centralizer, the matching relation, ambient generation and the final
Borel contradiction remain with qt-e-14315-eight-borel-exclusion.
Source: Aschbacher--Smith F.4.35, p.292; 14.2.18--19 and 14.3.15, pp.987,994.
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

/-- Every conjugate returning to the literal component core has a long-root
mark and an intrinsic quotient orbit of size at most nine. -/
theorem source_eight_marked_core_fusion
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T:Subgroup G)))
    (q : K.pCoreIn 2) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z (q:G)) :
    ∃ v : radical P .arms,
      v.val=(r.left ⟨q,(show K≤K ⊔ (T:Subgroup G) from le_sup_left) (pCoreIn_le 2 K q.property)⟩).val ∧
      IsLongRootInvolution 1 Nat.zero_lt_one v.val ∧
      (ArmsOrbit.points (ArmsOrbit.point v)).ncard≤9 := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have hq : (q:G)∈(K ⊔ (T:Subgroup G)).pCoreIn 2 := by
    simpa only [hjoin] using q.property
  let qH : (K ⊔ (T:Subgroup G)).pCoreIn 2 := ⟨q,hq⟩
  exact ⟨EightLargeParabolic.firstCoreEquiv r qH,
    EightLargeParabolic.firstCoreEquiv_val r qH,
    EightLargeParabolic.source_core_fusion_isLongRoot hG hempty hM hu hmany hcard e hH r qH hz hz1 hconj,
    EightLargeParabolic.source_core_fusion_orbit_bound hG hempty hM hu hmany hcard e hH r qH hz hz1 hconj⟩

/-- The entire short-root quotient orbit, including both central lifts, is
excluded on the original ComponentLift/EightImageRow, also for cubic Mc. -/
theorem source_eight_marked_short_orbit_not_fused
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T:Subgroup G)))
    (q : K.pCoreIn 2) {z : G} (hz : z∈centralInvolutions T) (hz1 : z≠1)
    (hconj : IsConj z (q:G)) (v : radical P .arms)
    (hv : v.val=(r.left ⟨q,(show K≤K ⊔ (T:Subgroup G) from le_sup_left) (pCoreIn_le 2 K q.property)⟩).val)
    (d : ExtensionField P) (hd : d≠0)
    (hshort : ArmsOrbit.point v∈ArmsOrbit.points (ArmsOrbit.point ⟨_,ArmsOrbit.short_two_mem d⟩)) : False := by
  obtain ⟨v',hv',_,hb⟩ := source_eight_marked_core_fusion hG T hempty hM hu hmany hcard e hK h8 r q hz hz1 hconj
  have he : v'=v := Subtype.ext (hv'.trans hv.symm)
  rw [he] at hb
  have hl := ArmsOrbit.short_orbit_point_lower d hd _ hshort
  omega
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
