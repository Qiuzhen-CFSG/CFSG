module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Inputs
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.MSBridge
public import CFSG.Quasithin.Chapter14.Section06.SourceClassificationComplete
public import Theory.GroupTheory.NormalCentralQuotientAction.KernelCriterion
public import Theory.SpecificGroups.FFG2DerivedCenter

/-!
# The actual G₂ component in the second-parabolic construction

The full derived-G₂ quotient is centerless. Thus its central-core marking
uses exactly the original two-core, and the C.2.7 component-radical product
is a small MS-pair. Applying the independently supplied whole-core
reconstruction gives the genuine short block on this same component.
The module is the six-dimensional trace-zero quotient, with its original
conjugation action; the central fixed subgroup of the entire U-layer is
not discarded.

Source: Aschbacher--Smith, C.1.30--32, pp.135--136, and original
14.6.10(5), printed p.1029.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u

namespace G2SecondParabolic
variable {L : Type*} [Group L]

/-- Recover the central-core equality from the supplied full quotient mark. -/
theorem centralPreimage_eq_core
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    centralPreimage (pCore 2 L) = pCore 2 L := by
  apply centralPreimage_eq_of_center_quotient_eq_bot
  apply bot_unique
  intro x hx
  have he : e x ∈ center (commutator (Atlas.G2.Model (ZMod 2))) :=
    (Subgroup.centerCongr e ⟨x,hx⟩).property
  rw [Theory.SpecificGroups.g2_derived_two_center_eq_bot, mem_bot] at he
  exact mem_bot.mpr (e.injective (he.trans e.map_one.symm))

/-- The reconstruction marking retains the original quotient projection. -/
@[expose] def centralCoreMarking
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  (QuotientGroup.quotientMulEquivOfEq (centralPreimage_eq_core e)).trans e

theorem centralCoreMarking_apply
    (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) (l : L) :
    centralCoreMarking e (QuotientGroup.mk' (centralPreimage (pCore 2 L)) l) =
      e (QuotientGroup.mk' (pCore 2 L) l) := rfl

end G2SecondParabolic

variable {G : Type u} [Group G] [Finite G]

/-- C.2.7 plus the full derived-G₂ quotient gives the literal reconstructed
block, conditional only on the independent whole-core theorem. -/
theorem g2_block_from_c27
    (hg : G2ReconstructionInput.{u} KnownSimple.IsKnownSimple)
    {H R M K : Subgroup G} (h : Input KnownSimple.IsKnownSimple H R M K)
    (hr : ChapterC.MSOddIndexRadical (R.subgroupOf H))
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ChapterC.IsG2TwoBlock K := by
  let eZ := G2SecondParabolic.centralCoreMarking eK
  have hm := smallMSPair_from_c27 h hr (Or.inr (Or.inr ⟨eZ⟩))
  have r := hg G K R hm eZ
  obtain ⟨m⟩ := r.model
  have hs := hm.short_of_core r.elementary r.central h.quasisimple m.g2_irreducible
  exact ChapterC.IsG2TwoBlock.of_model hs ⟨m⟩

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The original U3 Sylow and intersection-escape theorems discharge the
local premises of reconstruction on the actual generated component. -/
theorem source_second_parabolic_g2_block_of_reconstruction
    (hg : G2ReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M))
    (he : Nonempty ((sourceGeneratedComponent T M Mc I d.H2 ⧸
      pCore 2 (sourceGeneratedComponent T M Mc I d.H2)) ≃*
        commutator (Atlas.G2.Model (ZMod 2)))) :
    ChapterC.IsG2TwoBlock (sourceGeneratedComponent T M Mc I d.H2) := by
  have hlocal := source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab
    H hH d.u d.mem_span d.local_normalizer
  have hout := source_second_parabolic_intersection_escape
    hG T hempty hM hunique hmany hcard e hab H hH d I hI
  obtain ⟨hi,hr,_⟩ := source_generated_parabolic_ms_inputs
    hG T hempty hM hunique hmany hcard e hab H hH d.u d.mem_span d.index
    d.moves_core d.product_moves_core d.local_normalizer hlocal I d.H2 hI hout
    d.quotient_sylow d.le_quotient_centralizer d.quotient_model d.outside
    d.core_index d.module_rank
  exact g2_block_from_c27 hg hi hr he.some

end CFSG.Quasithin.Chapter14.Section06
