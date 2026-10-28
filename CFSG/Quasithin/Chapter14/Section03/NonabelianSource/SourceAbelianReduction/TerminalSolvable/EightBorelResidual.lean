module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelCoreAction
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.FirstResidual

/-!
# Identifying the original eight-row component with its Sylow join

The actual dotted-kernel comparison and minimality proof identify the embedded
O² residual of H = K join T with K. Perfectness of the marked first triality
parabolic then gives H = K and hence T ≤ K. The extraspecial core comparison
and its ambient normalizer now apply literally to K. Source 1.2.4 supplies its
unique normal containing C-component in Mc, and the actual quotient Sylow is E₈.

These prove the residual and Sylow premises of source 14.2.18 for the original
ComponentLift/EightImageRow. The marked realization is still the independent
earlier input. Non-enlargement, the cubic extension, ambient recognition and
terminal exclusion remain with qt-e-14315-eight-borel-exclusion.
Source: Aschbacher--Smith 14.2.16--18 and 14.3.15, pp.986--987,994.
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

/-- Perfectness of the marked first endpoint identifies it with the actual
component lift, using its already proved embedded O² identity. -/
theorem source_eight_marked_join_eq
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    K ⊔ (T : Subgroup G) = K :=
  (EightLargeParabolic.first_residual_eq r).symm.trans
    (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).2.1

/-- The Sylow containment in 14.2.18 is now a conclusion on the literal K.
The core equality and its ambient normalizer therefore hold for K itself. -/
theorem source_eight_marked_component_structure
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    (T : Subgroup G) ≤ K ∧ Group.IsPerfect K ∧
      Mc.pCoreIn 2 = K.pCoreIn 2 ∧ normalizer (K.pCoreIn 2 : Set G) = Mc ∧
      IsExtraspecial 2 (K.pCoreIn 2) ∧ Nat.card (K.pCoreIn 2) = 512 := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  refine ⟨le_sup_right.trans_eq hjoin, ?_, ?_, ?_, ?_, ?_⟩
  · let := EightLargeParabolic.first_perfect r
    let f := MulEquiv.subgroupCongr hjoin
    exact Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  · simpa only [hjoin] using
      EightLargeParabolic.source_partner_core_eq hG hempty hM hu hmany hcard e hH r
  · simpa only [hjoin] using
      EightLargeParabolic.source_firstCore_normalizer_eq hG hempty hM hu hmany hcard e hH r
  · exact IsExtraspecial.of_mulEquiv
      (MulEquiv.subgroupCongr (congrArg (fun J : Subgroup G => J.pCoreIn 2) hjoin))
      (EightLargeParabolic.firstCore_extraspecial r)
  · simpa only [hjoin] using EightLargeParabolic.firstCore_card r

/-- Source 1.2.4 on the original component lift, before the remaining
non-enlargement step identifying the containing component with K. -/
theorem source_eight_marked_normal_containing_component
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    ∃! C : Subgroup Mc, C.IsCComponent ∧ K.subgroupOf Mc ≤ C ∧ C.Normal := by
  have hjoin := source_eight_marked_join_eq hG T hempty hM hu hmany hcard e hK h8 r
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  simpa only [hjoin] using EightLargeParabolic.source_first_normal_containing_component
    hG hempty hM hu hmany hcard e hH r


/-- The original component supplies the elementary order-eight Sylow in the
same partner quotient used by the faithful core action. -/
theorem source_eight_marked_partner_quotient_sylow
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    ∃ S : Sylow 2 (Mc ⧸ pCore 2 Mc),
      (S : Subgroup (Mc ⧸ pCore 2 Mc)) =
        ((T : Subgroup G).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) ∧
      IsElementaryAbelian 2 S ∧ Nat.card S = 8 := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact ⟨EightLargeParabolic.sourcePartnerQuotientSylow
    hG hempty hM hu hmany hcard e hH, rfl,
    EightLargeParabolic.source_partner_quotient_sylow
      hG hempty hM hu hmany hcard e hH r⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
