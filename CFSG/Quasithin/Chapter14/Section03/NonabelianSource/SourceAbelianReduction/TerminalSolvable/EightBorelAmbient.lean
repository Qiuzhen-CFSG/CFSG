module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelExtremality
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.PlainGeneration

/-!
# Ambient short-centralizer containment for the original eight-field component

Apply the F.4.42 nonsplitting proof to the same original component and
endpoint marking. The local two-core centralizes the actual four-plane,
and the local short centralizer is five-free, in both partner cases.
When Mc equals K join T, the full ambient short centralizer lies in the
second endpoint and the original two endpoints generate G.

The cubic partner comparison, matching sixth-power relations, triality
recognition and final Borel contradiction remain. The genuine marked
realization is still explicit and must be supplied by its existing producer.
Source: Aschbacher--Smith F.4.42, 14.2.18--19 and 14.3.15,
printed pp.295,987,994.
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

local notation "P" => _root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one

/-- The actual component's local centralizer has the two inputs used to
exclude the larger Bender normal closure, for either partner alternative. -/
theorem source_eight_marked_short_bender_inputs
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (a : _root_.Triality.Standard.ExtensionField P) (ha : a ≠ 0) :
    let L := EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T : Subgroup G))
    let C := centralizer ({EightLargeParabolic.markedShortRoot r a} : Set L)
    pCore 2 C ≤ centralizer (EightLargeParabolic.markedShortPlane r a ha : Set C) ∧
      ¬ 5 ∣ Nat.card C := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact ⟨EightLargeParabolic.marked_short_core_centralizes_plane r hH.1.1.2 a ha,
    EightLargeParabolic.marked_short_five_free r a ha⟩

/-- Full ambient F.4.42 containment on the original component when its
first endpoint is the complete long centralizer. -/
theorem source_eight_marked_short_ambient_le_of_partner_eq
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (hplain : Mc = K ⊔ (T : Subgroup G))
    (a : _root_.Triality.Standard.ExtensionField P) (ha : a ≠ 0) :
    centralizer ({(EightLargeParabolic.markedShortRoot r a : G)} : Set G) ≤
      EightLargeParabolic.secondParabolic T M Mc (K ⊔ (T : Subgroup G)) := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact EightLargeParabolic.source_short_centralizer_le_of_partner_eq
    hG hempty hM hu hmany hcard e hH r hplain a ha

/-- Both original generated groups equal G in the plain partner case. -/
theorem source_eight_marked_generated_eq_top_of_partner_eq
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G)))
    (hplain : Mc = K ⊔ (T : Subgroup G)) :
    Mc ⊔ M = ⊤ ∧
      K ⊔ EightLargeParabolic.secondParabolic T M Mc K = ⊤ := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  refine ⟨EightLargeParabolic.source_extended_eq_top_of_partner_eq
    hG hempty hM hu hmany hcard e hH r hplain,?_⟩
  have hh := EightLargeParabolic.source_generated_eq_top_of_partner_eq
    hG hempty hM hu hmany hcard e hH r hplain
  rwa [hjoin] at hh

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
