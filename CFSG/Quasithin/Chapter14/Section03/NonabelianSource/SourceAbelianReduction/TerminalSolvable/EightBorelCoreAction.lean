module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.EightBorelMarked
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.CoreAction

/-!
# Core equality and the faithful partner action on the literal eight-row lift

The actual dotted-kernel proof supplies minimality of H = K join T. Applying
the marked core comparison to this H identifies the two-core of Mc and the
ambient normalizer of O₂(H). The induced action on O₂(Mc)/Z(O₂(Mc)) has
kernel O₂(Mc), and the original first endpoint has action image PSL₂(8).

These discharge the core-equality and faithful-action premises at the start of
original 14.2.18 for the exact ComponentLift/EightImageRow consumer of 14.3.15.
The marked realization remains an explicit earlier input. The remaining local
extension, ambient recognition and Borel exclusion stay with
qt-e-14315-eight-borel-exclusion; this module does not assert their completion.
Source: Aschbacher--Smith 14.2.16,14.2.18 and 14.3.15, pp.986--987,994.
-/

@[expose] public noncomputable section
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

/-- The actual component join supplies all original applicability hypotheses. -/
theorem source_eight_marked_core_rigidity
    (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    Mc.pCoreIn 2 = (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      normalizer ((K ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) = Mc ∧
      IsExtraspecial 2 (pCore 2 Mc) ∧ Nat.card (pCore 2 Mc) = 512 ∧
      (EightLargeParabolic.partnerCoreAction Mc).ker = pCore 2 Mc ∧
      IsElementaryAbelian 2 (EightLargeParabolic.PartnerCoreModule Mc) ∧
      Nat.card (EightLargeParabolic.PartnerCoreModule Mc) = 256 := by
  have hH := (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1
  exact ⟨EightLargeParabolic.source_partner_core_eq hG hempty hM hu hmany hcard e hH r,
    EightLargeParabolic.source_firstCore_normalizer_eq hG hempty hM hu hmany hcard e hH r,
    EightLargeParabolic.source_partner_core_extraspecial hG hempty hM hu hmany hcard e hH r,
    EightLargeParabolic.source_partner_core_card hG hempty hM hu hmany hcard e hH r,
    EightLargeParabolic.source_partner_core_action_kernel hG hempty hM hu hmany hcard e hH r,
    EightLargeParabolic.source_partner_core_module hG hempty hM hu hmany hcard e hH r⟩

/-- Conjugation by the literal K join T on the original partner-core module. -/
def eightFirstCoreAction (hK : ComponentLift F g K) (h8 : EightImageRow F K) :
    (K ⊔ (T : Subgroup G) : Subgroup G) →*
      MulAut (EightLargeParabolic.PartnerCoreModule Mc) :=
  EightLargeParabolic.firstCoreAction hG hempty hM hu hmany hcard e
    (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1

/-- The marked first image is a concrete PSL₂(8) in the same action as Mc. -/
def eightFirstActionImageEquiv (hK : ComponentLift F g K) (h8 : EightImageRow F K)
    (r : EightLargeParabolic.MarkedTriality T M Mc (K ⊔ (T : Subgroup G))) :
    (eightFirstCoreAction hG T hempty hM hu hmany hcard e hK h8).range ≃*
      Theory.PSL2.BinaryGroup 3 :=
  EightLargeParabolic.sourceFirstActionImageEquiv hG hempty hM hu hmany hcard e
    (source_eight_join_minimal hG T hempty hM hu hmany hcard e hK h8).1 r

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
