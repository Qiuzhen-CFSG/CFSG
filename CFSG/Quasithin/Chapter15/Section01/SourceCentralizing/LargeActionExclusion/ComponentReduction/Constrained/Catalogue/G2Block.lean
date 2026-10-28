module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ReducedModels
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.G2.Reconstruction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Source

/-!
# Whole G₂ block reconstruction at the original component

The actual FF map K/O₂(K) → K* is a perfect central cover. In the
G₂(2)′ row its kernel is a two-group, so the trivial two-core of the
domain makes that map an isomorphism, with the original marking retained.

For the selected component, this quotient supplies the proved cubic
normalization facts and hence the literal C.2.7 input. M_Z contains the
original Sylow subgroup and has two-core Q₁, so it supplies MS2(a).
The completed G₂ reconstruction theorem now applies to LQ₁ and recovers
the whole blockU, its central action, and the canonical natural module.
No Sylow assumption on Q₁ or general MS-classification premise is used.

Both original primes and both exchanged plane sizes are retained. The
original-marker consumer reconstructs the actual block, and the exchanged
consumer applies its centralizer obstruction directly to the FF row.
The positive parabolic and centralizer clauses, the other small blocks,
and general-family Borel placement remain with the catalogue owner.
Original 15.1.14 retains its existing producer and final assembly owner.

Source: Aschbacher--Smith 15.1.20(2b), pp.1094--1095; C.1.31--32 and
C.2.7, pp.135--136,145--147. Whole-core reconstruction is the proved
MS93 G₂ theorem consumed through the existing C.2.7 bridge.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Theory.SpecificGroups.BinaryComponentResidual
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original G₂ comparison loses no further central kernel. -/
theorem NormalizerAction.g2Derived_core_bijective
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : d.normalizerImage K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    Function.Bijective a.coreToImage := by
  let c : PerfectCentralCovering.Cover (K ⧸ pCore 2 K)
      (commutator (Atlas.G2.Model (ZMod 2))) := {
    toMonoidHom := e.toMonoidHom.comp a.coreToImage
    surjective := e.surjective.comp a.coreToImage_surjective
    isPerfect := hq.toIsPerfect
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      exact a.coreToImage_ker_central hq }
  have hk := BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup c
  have hz : c.toMonoidHom.ker = ⊥ := bot_unique
    ((show c.toMonoidHom.ker ≤ pCore 2 (K ⧸ pCore 2 K) from
      le_sSup ⟨inferInstance,hk⟩).trans_eq (pCore_quotient_pCore_eq_bot 2))
  have hi : Function.Injective c.toMonoidHom := (MonoidHom.ker_eq_bot_iff _).mp hz
  exact ⟨fun _ _ hh => hi (congrArg e hh),a.coreToImage_surjective⟩

/-- The G₂ FF image identifies the actual two-core quotient through its original map. -/
@[expose] noncomputable def NormalizerAction.g2Derived_coreEquiv
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : d.normalizerImage K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2)) :=
  (MulEquiv.ofBijective a.coreToImage (a.g2Derived_core_bijective hq e)).trans e

@[simp] theorem NormalizerAction.g2Derived_coreEquiv_mk
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : d.normalizerImage K ≃* commutator (Atlas.G2.Model (ZMod 2))) (k : K) :
    a.g2Derived_coreEquiv hq e (QuotientGroup.mk' (pCore 2 K) k) =
      e (d.toNormalizerImage K k) := rfl

/-- M_Z itself supplies the original odd-index two-core witness. -/
theorem constrained_msOddIndexRadical (d : CaseIComponentData T M Mc V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hs : Chapter1.IsSylowIn 2 d.S d.G1)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    ChapterC.MSOddIndexRadical (d.Q1.subgroupOf d.G1) := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hSM : d.S ≤ d.MZ := le_inf d.S_le_G1 (d.S_le_T.trans hTMc)
  obtain ⟨P,hP⟩ := hs
  apply msOddIndexRadical_of_first_core hi d.MZ inf_le_left le_rfl P
  · intro x hx
    exact hSM (hP ▸ mem_map_of_mem d.G1.subtype hx)
  · rfl

/-- The complete original G₂ block reconstruction, using the actual M_Z and Q₁. -/
theorem constrained_g2_block_of_core_quotient (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    (hq : IsQuasisimple (d.L ⧸ pCore 2 d.L))
    (hQne : d.Q1 ≠ ⊥)
    (hc : d.Q1.characteristicNormalizerClosure ≤ Mc)
    (hn : d.G1 ⊓ normalizer (d.Q1 : Set G) = d.MZ)
    (hs : Chapter1.IsSylowIn 2 d.S d.G1)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : (d.L ⧸ pCore 2 d.L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ChapterC.IsG2TwoBlock d.L := by
  have hi := d.constrained_input hG h hq hQne hc hn (Facts.of_equiv e g2) hf
  exact Chapter14.Section06.g2_block_from_c27 g2Reconstruction_knownSimple hi
    (d.constrained_msOddIndexRadical hi hs hu) e

/-- The original FF G₂ row reconstructs the whole block, retaining either prime. -/
theorem PreExclusionSource.constrained_g2_block
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ChapterC.IsG2TwoBlock d.L := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
  exact d.constrained_g2_block_of_core_quotient hG h s.quasisimple s.core_nontrivial
    s.characteristic_control s.core_normalizer s.centralizer_sylow hu hf
    (a.g2Derived_coreEquiv s.quasisimple e)

/-- The same reconstruction holds for either later exchanged plane size. -/
theorem ExchangedSource.constrained_g2_block
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ChapterC.IsG2TwoBlock d.L := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
  exact d.constrained_g2_block_of_core_quotient hG h s.quasisimple s.core_nontrivial
    s.characteristic_control s.core_normalizer s.centralizer_sylow hu hf
    (a.g2Derived_coreEquiv s.quasisimple e)

/-- The exchanged centralizer obstruction now applies directly to the FF image. -/
theorem ExchangedSource.no_g2_image_centralizers
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ¬ d.ConstrainedCentralizerIdentity :=
  s.no_constrained_g2_centralizers hG hM.1.2 h
    (s.constrained_g2_block hG hempty hM hJ hu h hf e)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- G₂ block reconstruction at the actual original marker, retaining the row
and either prime. The independent original 15.1.14 premise is unchanged. -/
theorem PreparedChosenModule.source_preExclusion_constrained_g2_block
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        Nonempty (d.normalizerImage d.L ≃* commutator (Atlas.G2.Model (ZMod 2))) →
        ChapterC.IsG2TwoBlock d.L) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf ⟨e⟩ =>
    s.constrained_g2_block (h := h) hG hempty hM hJ hu hf e⟩
end CFSG.Quasithin.Chapter15.Section01
