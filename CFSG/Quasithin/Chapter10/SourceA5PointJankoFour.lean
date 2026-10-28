module
public import CFSG.Quasithin.Chapter10.SourceA5PointCoreCenter
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CoreCenter.A5Overgroup

/-!
# Source A₅ point configurations in the marked J₄ max4 local

The source fully moved elementary module forces the center of the literal
image's two-core to have at least sixteen elements. A marked normal overgroup
of the J₄ max4 two-core has the same core, whose center has at most eight.
This excludes the marked local; the source placement remains an explicit
mathematical premise, rather than being inferred from the ambient J₄ label.

Source: Aschbacher–Smith A.3.14(10) and source 10.2.9, pp.750–751.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter10
open Janko4.LocalStructure.SymmetricLinear
variable {G : Type*} [Group G] [Finite G] {L I : Subgroup G}
  {T : Sylow 2 G}
  (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The literal image cannot be a marked normal overgroup of the max4 core. -/
theorem source_a5_not_jankoFour_marked_normal_overgroup
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I)
    (H : Subgroup max4Subgroup) [H.Normal] (hQ : pCore 2 max4Subgroup ≤ H)
    (f : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃* H) : False := by
  have hl : 16 ≤ Nat.card (center (pCore 2 H)) :=
    source_a5_marked_core_center_card (B := H) D e hLI f
  have hu := normal_overgroup_twoCore_center_card_le_eight H hQ
  omega

include D in
/-- Specialization to the actual A₅-factor preimage under the max4 quotient. -/
theorem source_a5_not_jankoFour_a5Preimage
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I)
    (f : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃* a5Preimage) : False := by
  exact source_a5_not_jankoFour_marked_normal_overgroup D e hLI
    a5Preimage twoCore_le_a5Preimage f
end CFSG.Quasithin.Chapter10
