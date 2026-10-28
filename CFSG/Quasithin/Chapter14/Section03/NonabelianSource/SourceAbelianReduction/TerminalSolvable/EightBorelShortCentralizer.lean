module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelFusionControl
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.ShortPlane

/-!
# The local short centralizer on the original eight-field component

The short-root involution is pulled back through the same original right
endpoint marking. Its local centralizer identifies with the entire native
short centralizer, and its intersection with the original T is Sylow.
Its normal elementary four-group lies in the derived subgroup of its two-core.
The original central involution generates this plane as its local normal
closure; all three nonidentity elements are conjugate inside that same local
short centralizer.
This supplies the local centralizer and nonsplitting inputs for the original
F.4.42 application, including the cubic partner case.

The full ambient short centralizer, matching sixth-power relation, ambient
generation and original Borel contradiction remain to be established.
The genuine marked realization remains explicit and is owned by
qt-e-1427-eight-amalgam-recognition.
Source: Aschbacher--Smith F.4.27(4)(ii), F.4.40--42, 14.2.18--19 and 14.3.15,
printed pp.288,294--295,987,994.
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



/-- The local short-centralizer inputs on the literal ComponentLift/EightImageRow.
The full ambient centralizer is not substituted for this local group. -/
theorem source_eight_marked_short_centralizer
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : _root_.Triality.Standard.ExtensionField
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one)) (ha : a ≠ 0) :
    let H := K ⊔ (T : Subgroup G)
    let L := EightLargeParabolic.secondParabolic T M Mc H
    let t := EightLargeParabolic.markedShortRoot r a
    let C := centralizer ({t} : Set L)
    let V := EightLargeParabolic.markedShortPlane r a ha
    orderOf (t : G) = 2 ∧ (t : G) ∈ (T : Subgroup G) ∧
      (∃ S : Sylow 2 C, (S : Subgroup C) = ((T : Subgroup G).subgroupOf L).subgroupOf C) ∧
      V.Normal ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 4 ∧ V ≤ ⁅pCore 2 C,pCore 2 C⁆ := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact ⟨EightLargeParabolic.markedShortRoot_order r a ha,
    EightLargeParabolic.markedShortRoot_mem_sylow r hH.1.1.2 a,
    EightLargeParabolic.marked_short_local_sylow r hH.1.1.2 a ha,
    EightLargeParabolic.marked_short_plane_structure r a ha⟩

/-- F.4.42's plane is the normal closure of the original central involution
inside the literal component's local short centralizer, with its full orbit. -/
theorem source_eight_marked_short_plane
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : _root_.Triality.Standard.ExtensionField
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one)) (ha : a ≠ 0)
    {z : G} (hz : z ∈ centralInvolutions T) (hz1 : z ≠ 1) :
    let L := EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T : Subgroup G))
    let C := centralizer ({EightLargeParabolic.markedShortRoot r a} : Set L)
    let V := EightLargeParabolic.markedShortPlane r a ha
    (∃ zC : C, (zC.val : G) = z ∧ normalClosure ({zC} : Set C) = V) ∧
      (∀ x : C, x ∈ V → (x.val : G) ≠ 1 →
        ∃ c : C, (c.val : G) * z * (c.val : G)⁻¹ = (x.val : G)) := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have hzH : z ∈ EightLargeParabolic.firstCoreCenter (K ⊔ (T : Subgroup G)) := by
    rw [EightLargeParabolic.source_firstCore_center hG hempty hM hu hmany hcard e hH r]
    exact hz
  obtain ⟨zC,hzC,_⟩ := EightLargeParabolic.marked_short_plane_contains_center
    r hH.1.1.2 a ha hzH hz1
  refine ⟨⟨zC,hzC,?_⟩,?_⟩
  · exact EightLargeParabolic.marked_short_plane_normalClosure r hH.1.1.2 a ha zC
      (hzC.symm ▸ hzH) (hzC.symm ▸ hz1)
  · exact fun x hx hx1 => EightLargeParabolic.marked_short_plane_orbit r hH.1.1.2
      a ha hzH hz1 x hx hx1

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
