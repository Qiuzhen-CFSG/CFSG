module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.OriginalF916
/-!
# Original 15.3.64 with its quadratic actor placed in the edge core

Original 15.3.48 and the ordinary residual identity of 15.3.49 give the
literal F.9.1 setup. The original fusion and abelian-span conclusions give
F.9.8. The specialized F.9.16 producer then supplies the representation on
U_H/Z and a common quadratic actor in the prescribed edge two-core. Its
placement is retained for the component calculations of 15.3.65.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.64, printed p.1151, and F.9.16(3), printed p.324.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.OriginalSource
open ChapterA.Section05To06 ModuleBound FusionCore.CosetSetup
variable {G : Type*} [Group G] [Finite G]

/-- Original48 supplies every F.9.1 clause; ordinary49 removes its case side-condition. -/
theorem f91_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    (h49 : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    [IsElementaryAbelian 2 d.V]
    {H : Subgroup G} (hH : H ∈ sylowOutsideFamily d.T d.M) (hHMc : H ≤ d.Mc) :
    SourceF91 d.T d.Y d.V d.ZS d.Z H := by
  apply SourceF91.ofF91
  apply FusionCore.CosetSetup.OriginalSource.source_hypothesis hG d hempty hM hu hmany
    hfixed H hH.1.2 hHMc hH.2
  intro _
  rw [← h49]
  apply le_trans (core_le_sylow_of_invariant d.Y d.T _) hH.1.2
  exact d.sylow_le.trans ((normal_subgroupOf_iff_le_normalizer
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)).mp (residualY_normal d.M d.Mc))

/-- Original64 on any selected H≤Mc, retaining the literal placed actor required by65. -/
theorem bounded_action_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    (h49 : d.Y.pCoreIn 2 = d.Y ⊓ centralizer (d.V : Set G))
    [IsMulCommutative (conjugateSpanBy d.V d.Mc)]
    {H : Subgroup G} (hH : H ∈ sylowOutsideFamily d.T d.M) (hHMc : H ≤ d.Mc) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy d.ZS H),
      let := hU
      ∃ a : LocalQuotientAction H (conjugateSpanBy d.ZS H) d.Z,
        ∃ B : Subgroup H,
          B ≤ (((d.Y ⊔ (d.T : Subgroup G)) ⊓ H).pCoreIn 2).subgroupOf H ∧
          IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
          IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
          fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ≤
            2 * rank (B.map (QuotientGroup.mk' (pCore 2 H))) := by
  let := d.action.elementary
  let : IsMulCommutative (conjugateSpanBy d.V H) :=
    conjugateSpanBy_isMulCommutative_of_le le_rfl hHMc
  have h91 := f91_from_original hG d hempty hM hu hmany hfixed h49 hH hHMc
  have h62 := intersecting_conjugates_commute_from_original hG d hempty hM hu hmany hfixed
  have h47 := commutator_alternative_from_original hG d hM hfixed
  obtain ⟨hU,a,_⟩ := OriginalF916.original_bounded_action h91 h62 h47
  let := hU
  exact ⟨hU,a,OriginalF916.original_witness h91 h62 h47 a⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.OriginalSource
