module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SixParabolics
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SixRemainder

/-!
# Ordinary A₆ geometry on the original source and catalogue remainder

The ordinary A₆ block now supplies both literal parabolics, their common
quotient marking, the centralizer of the original central-involution seed,
and the O^{3′} residual-centralizer identity. The original marker application
retains either source prime and every ambient hypothesis.

Applying the independently owned whole-core reconstruction to the remaining
six-point MS row leaves only the exceptional cubic A₆ block. This is a
conditional reduction: AlternatingSixReconstructionInput still belongs to
qt-e-ms-small-a6-reconstruction, and its discharge and the exceptional
exclusion are necessary before catalogue exhaustiveness. Original 15.1.14
also remains explicit for its existing producer and assembly owner.

Source: Aschbacher--Smith 15.1.20(2b), 15.1.22(2), printed pp.1094--1100.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Theory.SpecificGroups.SymmetricSix
universe u
variable {G : Type u} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- With the independent whole-core reconstruction, ordinary A₆ geometry
removes that branch. The cubic block and its original MS marking remain. -/
theorem PreExclusionSource.constrained_catalogue_or_exceptional_six_of_reconstruction
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    d.ConstrainedAlternatives ∨
      (IsExceptionalAhat6Block d.L ∧
        Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
        SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
        ∃ e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃* alternatingGroup (Fin 6),
          ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
            ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
              e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k))) := by
  rcases s.constrained_catalogue_or_six_ms (h := h)
    hG hempty hM hJ hu hne hmany hfull hres hf with hc | ⟨hi,hms,e,t,ht⟩
  · exact Or.inl hc
  · rcases s.constrained_six_blocks_of_reconstruction (h := h)
      ha hG hempty hM hJ hu hf e with hb | hb
    · obtain ⟨_,_,_,_,_,_,_,_,_,_,hc⟩ := s.constrained_six_of_block (h := h)
        hG hempty hM hJ hu hfull hb
      exact Or.inl hc
    · exact Or.inr ⟨hb,hi,hms,e,t,ht⟩

end CaseIComponentData

/-- The actual original marker has opposite A₆ parabolics under the same FF
marking, once its whole ordinary block is supplied. This is valid before
exchanged selection at both original primes. -/
theorem PreparedChosenModule.source_preExclusion_constrained_six_of_block
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
      (IsAlternatingBlock d.L 6 →
        ∀ e : d.normalizerImage d.L ≃* alternatingGroup (Fin 6),
          ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 6),
            (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
            (let q := t.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
             ∃ g : alternatingGroup (Fin 6),
               (((d.ML.subgroupOf d.L).map q = (MulAut.conj g).mapSubgroup a6DuadStabilizer ∧
                 ((M ⊓ d.L).subgroupOf d.L).map q = (MulAut.conj g).mapSubgroup a6SynthemeStabilizer) ∨
                ((d.ML.subgroupOf d.L).map q = (MulAut.conj g).mapSubgroup a6SynthemeStabilizer ∧
                 ((M ⊓ d.L).subgroupOf d.L).map q = (MulAut.conj g).mapSubgroup a6DuadStabilizer))) ∧
            Nat.card d.plusOmega = 2 ∧
            d.ML = d.L ⊓ centralizer (centralInvolutions T : Set G) ∧
            d.IsSourceParabolic d.ML ∧ d.IsSourceParabolic (M ⊓ d.L) ∧
            (M ⊓ d.L) ⊔ d.ML = d.L ∧
            d.ConstrainedCentralizerIdentity ∧ d.ConstrainedAlternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro hb e
  obtain ⟨t,ht⟩ := s.constrained_six_core_marking (h := h) hG hempty hM hJ hu hb e
  obtain ⟨hc,hseed,_,_,_,hgen,hP,hQ,_,hcent,halt⟩ :=
    s.constrained_six_of_block (h := h) hG hempty hM hJ hu hfull hb
  exact ⟨t,ht,s.constrained_six_marked_parabolics (h := h)
    hG hempty hM hJ hu hfull hb t,hc,hseed,hP,hQ,hgen,hcent,halt⟩

/-- Original-marker assembly consumes the ordinary A₆ geometry, retaining
both the independent reconstruction premise and the cubic block remainder. -/
theorem PreparedChosenModule.source_preExclusion_constrained_catalogue_or_exceptional_six_of_reconstruction
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
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
        d.ConstrainedAlternatives ∨
          (IsExceptionalAhat6Block d.L ∧
            Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L ∧
            SmallMSPair KnownSimple.IsKnownSimple d.L d.Q1 ∧
            ∃ e : (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L)) ≃* alternatingGroup (Fin 6),
              ∃ t : (d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 6),
                ∀ k : d.L, t (QuotientGroup.mk' (centralPreimage (pCore 2 d.L)) k) =
                  e (QuotientGroup.mk' (center (d.normalizerImage d.L)) (d.toNormalizerImage d.L k)))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf => s.constrained_catalogue_or_exceptional_six_of_reconstruction (h := h)
    ha hG hempty hM hJ hu hne hmany hfull hres hf⟩

end CFSG.Quasithin.Chapter15.Section01
