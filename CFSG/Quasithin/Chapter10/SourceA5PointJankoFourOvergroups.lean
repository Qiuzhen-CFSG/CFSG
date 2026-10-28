module
public import CFSG.Quasithin.Chapter10.SourceA5PointJankoFour
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.CoreOvergroupCenter

/-!
# The original A₅ image in overgroups of the J₄ max2 and max4 cores

The fully moved source module gives at least sixteen elements in the center
of the two-core of the literal image of L in I/Z(I). For the actual max2
and max4 carriers, any subgroup containing the ambient two-core has core
center of order at most two or eight, respectively. This excludes both
marked placements without assuming normality of the overgroup.

The embedding forms retain the original image homomorphism and require the
actual core to lie in its range. They do not infer this containment or local
placement from an ambient J₄ carrier label. Those source obligations remain
with the original Sylow/local-normalizer argument.

Source: Aschbacher–Smith A.3.12(17), A.3.14(10), and source 10.2.9,
printed pp.750–751. The previously proved normal-overgroup API is re-exported.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter10
open Janko4.LocalStructure Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
variable {G : Type*} [Group G] [Finite G] {L I : Subgroup G}
  {T : Sylow 2 G}
  (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The literal image cannot be an overgroup of the actual max4 two-core. -/
theorem source_a5_not_jankoFour_max4_core_overgroup
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I)
    (H : Subgroup max4Subgroup) (hQ : pCore 2 max4Subgroup ≤ H)
    (f : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃* H) : False := by
  have hl : 16 ≤ Nat.card (center (pCore 2 H)) :=
    source_a5_marked_core_center_card (B := H) D e hLI f
  have hu := overgroup_twoCore_center_card_le_eight H hQ
  omega

include D in
/-- The literal image cannot be an overgroup of the original ATLAS max2 two-core. -/
theorem source_a5_not_jankoFour_max2_core_overgroup
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I)
    (H : Subgroup sourceSubgroup) (hQ : pCore 2 sourceSubgroup ≤ H)
    (f : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃* H) : False := by
  have hl : 16 ≤ Nat.card (center (pCore 2 H)) :=
    source_a5_marked_core_center_card (B := H) D e hLI f
  have hu := max2_overgroup_twoCore_center_card_le_two H hQ
  omega

include D in
/-- The same max4 exclusion retaining the actual injective image homomorphism. -/
theorem source_a5_not_jankoFour_max4_core_embedding
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I)
    (f : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) →* max4Subgroup)
    (hf : Function.Injective f) (hQ : pCore 2 max4Subgroup ≤ f.range) : False := by
  exact source_a5_not_jankoFour_max4_core_overgroup D e hLI f.range hQ
    (MonoidHom.ofInjective hf)

include D in
/-- The same max2 exclusion retaining the actual injective image homomorphism. -/
theorem source_a5_not_jankoFour_max2_core_embedding
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I)
    (f : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) →* sourceSubgroup)
    (hf : Function.Injective f) (hQ : pCore 2 sourceSubgroup ≤ f.range) : False := by
  exact source_a5_not_jankoFour_max2_core_overgroup D e hLI f.range hQ
    (MonoidHom.ofInjective hf)

end CFSG.Quasithin.Chapter10
