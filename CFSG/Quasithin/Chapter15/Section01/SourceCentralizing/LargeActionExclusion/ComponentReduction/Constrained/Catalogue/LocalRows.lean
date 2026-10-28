module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.RankOneImage
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryParabolics
public import Theory.SpecificGroups.FFG2DerivedCenter
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Original quotient and parabolic rows on the whole local family

The reduced FF list now gives the literal source rows for every eligible
K in L(G₁,S), with no ambient C-component assumption on K. Rank-one image
recognition reconstructs the natural L₂ or A₅ block. The four small rows
identify K/O₂,Z(K), preserving the original core-to-FF comparison, including
the cubic A₆ covering outcome. In the binary linear rows the comparison
kernel vanishes, and both M_Z∩K and M∩K are proper flag parabolics under
the same isomorphism of K/O₂(K). The original Thompson commutator is retained.

The A₅ row has its exact Borel and centralizer. For the natural L₂ row,
this reduction retains the proved Borel bound and exact marked two-core;
the lower Borel containment remains open on the general local family.
The additional block and centralizer assertions of 15.1.20(2b) require
ambient C-componenthood and remain in the selected catalogue assembly.
In particular neither this reduction nor a central-quotient marking
supplies the independent whole-core A₆ reconstruction input.

The original-marker consumer preserves both source primes and the fixed
G₁,M_Z,S,Q₁, while the later exchanged consumer uses the same component.
Original 15.1.14 remains explicit for its existing producer and assembly.

Source: Aschbacher--Smith 15.1.20(2), printed pp.1094--1095;
15.1.22(3), printed pp.1098--1100, for the selected parabolic consumer.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private noncomputable def centerlessQuotientEquiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B) (hz : center B = ⊥) :
    (A ⧸ center A) ≃* B :=
  (QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e)).trans
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)

/-- The four actual central quotients in source 15.1.20(2b). -/
inductive LocalSmallCentralModel (A : Type*) [Group A] : Prop
  | alternatingSeven (equiv : A ≃* alternatingGroup (Fin 7))
  | linearThree (equiv : A ≃* SL(3,ZMod 2))
  | alternatingSix (equiv : A ≃* alternatingGroup (Fin 6))
  | g2DerivedTwo (equiv : A ≃* commutator (Atlas.G2.Model (ZMod 2)))

private theorem LocalSmallCentralModel.transport
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : LocalSmallCentralModel B) : LocalSmallCentralModel A := by
  cases h with
  | alternatingSeven t => exact .alternatingSeven (e.trans t)
  | linearThree t => exact .linearThree (e.trans t)
  | alternatingSix t => exact .alternatingSix (e.trans t)
  | g2DerivedTwo t => exact .g2DerivedTwo (e.trans t)

/-- A flag parabolic of an arbitrary local member, under its specified
literal two-core quotient marking. -/
@[expose] def LocalLinearParabolic {K : Subgroup G} {n : ℕ}
    (e : (K ⧸ pCore 2 K) ≃* SL(n,ZMod 2)) (P : Subgroup G) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ f : LinearFlag (ZMod 2) n k,
    ((P.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map e.toMonoidHom =
      f.stabilizer

/-- Both proper source intersections for every binary-linear local member.
The marking agrees with the original FF map on each element of K. -/
theorem localFamily_binary_linear_marked_parabolics (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (e : d.normalizerImage K ≃* SL(n,ZMod 2)) :
    ∃ t : (K ⧸ pCore 2 K) ≃* SL(n,ZMod 2),
      (∀ k : K, t (QuotientGroup.mk' (pCore 2 K) k) = e (d.toNormalizerImage K k)) ∧
      (d.MZ ⊓ K < K ∧ LocalLinearParabolic t (d.MZ ⊓ K)) ∧
      (M ⊓ K < K ∧ LocalLinearParabolic t (M ⊓ K)) := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  let t := (MulEquiv.ofBijective a.coreToImage
    (a.binary_linear_core_bijective hG h hK.1 hq hn e)).trans e
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hSM : d.S ≤ d.MZ := by
    refine le_inf d.S_le_G1 ?_
    intro x hx
    exact hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm)
  have hz : d.MZ ⊓ K < K := lt_of_le_of_ne inf_le_right
    (fun he => hout (he ▸ inf_le_left))
  have hm : M ⊓ K < K := lt_of_le_of_ne inf_le_right
    (fun he => d.localFamily_not_le_M hG hempty hM hu hK hout (he ▸ inf_le_left))
  exact ⟨t,fun _ => rfl,
    ⟨hz,d.localFamily_binary_flag hK (by omega) t _ (inf_le_inf_right K hSM) hz⟩,
    ⟨hm,d.localFamily_binary_flag hK (by omega) t _
      (inf_le_inf_right K (d.S_le_T.trans hM.1.2)) hm⟩⟩

/-- Full local-family source rows, with only the natural L₂ Borel equality
still pending. The small row asserts the source central quotient, not a
whole block outside the additional ambient C-component branch. -/
inductive LocalConstrainedRows (d : CaseIComponentData T M Mc V) (K : Subgroup G) : Prop
  | naturalTwo (n : ℕ) (block : IsL2EvenBlock K n)
      (borel_bound : d.MZ ⊓ K ≤ d.localSylowBorel K)
      (marked_core : (d.MZ ⊓ K).pCoreIn 2 = d.S ⊓ K)
  | alternatingFive (block : IsAlternatingBlock K 5)
      (borel : d.MZ ⊓ K = d.localSylowBorel K)
      (centralizing : d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G))
  | small (model : LocalSmallCentralModel (K ⧸ centralPreimage (pCore 2 K)))
      (equiv : (K ⧸ centralPreimage (pCore 2 K)) ≃*
        (d.normalizerImage K ⧸ center (d.normalizerImage K)))
      (marking : ∀ k : K, equiv (QuotientGroup.mk' (centralPreimage (pCore 2 K)) k) =
        QuotientGroup.mk' (center (d.normalizerImage K)) (d.toNormalizerImage K k))
  | linear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (imageEquiv : d.normalizerImage K ≃* SL(n,ZMod 2))
      (equiv : (K ⧸ pCore 2 K) ≃* SL(n,ZMod 2))
      (marking : ∀ k : K, equiv (QuotientGroup.mk' (pCore 2 K) k) =
        imageEquiv (d.toNormalizerImage K k))
      (marked_parabolic : d.MZ ⊓ K < K ∧ LocalLinearParabolic equiv (d.MZ ⊓ K))
      (selected_parabolic : M ⊓ K < K ∧ LocalLinearParabolic equiv (M ⊓ K))

private noncomputable def fiveLinearEquiv :
    alternatingGroup (Fin 5) ≃* SL(2,ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :=
  (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := ChapterB.QuasisimpleSource.BinaryField.four.Carrier) (by
      change Nat.card (GaloisField 2 2) = 4
      rw [GaloisField.card 2 2 (by decide)]
      decide)).some.symm.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm

/-- Source 15.1.20(2)'s group rows, with their actual original quotients,
rank-one blocks and binary flag parabolics, for all eligible K in L(G₁,S).
Only the lower natural-L₂ Borel containment is absent from this reduction. -/
theorem localFamily_constrained_rows (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ LocalConstrainedRows d K := by
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  refine ⟨a.movement.symm,?_⟩
  have rankOne (F : ChapterB.QuasisimpleSource.BinaryField)
      (e : d.normalizerImage K ≃* SL(2,F.Carrier)) : LocalConstrainedRows d K := by
    rcases d.localFamily_rankOne_block hG hempty hM hJ hu h hK hq hout hf F.Carrier e with
      ⟨n,hb⟩ | hb
    · exact .naturalTwo n hb
        ((d.localFamily_linearTwo_borel_bound hu hK hout hb).trans_eq
          (d.localSylowBorel_eq K).symm)
        (d.localFamily_linearTwo_core hu hK hout hb)
    · obtain ⟨hc,hborel⟩ := d.localFamily_alternatingFive_borel h hM.1.2 hu hK hq hout hb
      exact .alternatingFive hb (hborel.trans (d.localSylowBorel_eq K).symm) hc
  have small (hm : LocalSmallCentralModel (d.normalizerImage K ⧸ center (d.normalizerImage K))) :
      LocalConstrainedRows d K :=
    .small (hm.transport (a.coreCenterQuotientEquiv hq))
      (a.coreCenterQuotientEquiv hq) (a.coreCenterQuotientEquiv_mk hq)
  have linear {n : ℕ} (hn : n = 4 ∨ n = 5) (e : d.normalizerImage K ≃* SL(n,ZMod 2)) :
      LocalConstrainedRows d K := by
    obtain ⟨t,ht,hz,hm⟩ := d.localFamily_binary_linear_marked_parabolics
      hG hempty hM hJ hu h hK hq hout hf hn e
    exact .linear n hn e t ht hz hm
  cases d.localFamily_reduced_ff_model hG hempty hM hJ hu h hK hq hout hf with
  | linearTwo F e => exact rankOne F e
  | linearThree e =>
    exact small (.linearThree (centerlessQuotientEquiv e Matrix.PSL3Two.center_eq_bot))
  | g2DerivedTwo e =>
    exact small (.g2DerivedTwo (centerlessQuotientEquiv e
      Theory.SpecificGroups.g2_derived_two_center_eq_bot))
  | alternating n hn e =>
    rcases hn with rfl | rfl | rfl | rfl
    · exact rankOne ChapterB.QuasisimpleSource.BinaryField.four (e.trans fiveLinearEquiv)
    · exact small (.alternatingSix (centerlessQuotientEquiv e
        (alternatingGroup.center_eq_bot (by simp))))
    · exact small (.alternatingSeven (centerlessQuotientEquiv e
        (alternatingGroup.center_eq_bot (by simp))))
    · exact linear (Or.inl rfl) (e.trans
        (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans Atlas.Order20160A8.sl4TwoEquivPSL.symm))
  | linearFiveTwo e => exact linear (Or.inr rfl) e
  | tripleSix _ e => exact small (.alternatingSix e)
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Original-source specialization, with either source prime and the same
selected component. This does not discharge whole-core A₆ reconstruction. -/
theorem PreExclusionSource.constrained_local_rows
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    ⁅d.L,elementaryAbelianMaxJ d.S⁆ = d.L ∧ LocalConstrainedRows d d.L :=
  d.localFamily_constrained_rows hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf

/-- The later exchanged selection consumes the same quotient markings and
source intersections; no earlier prime-five argument depends on this export. -/
theorem ExchangedSource.constrained_local_rows
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    ⁅d.L,elementaryAbelianMaxJ d.S⁆ = d.L ∧ LocalConstrainedRows d d.L :=
  d.localFamily_constrained_rows hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Stellmacher
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies these quotient and parabolic rows for
EVERY eligible K in the fixed L(G₁,S), while preserving Z₁, row and prime.
The natural-L₂ lower Borel containment and the extra ambient-component
block clauses are separate from this general-family reduction. Original
15.1.14 remains explicit for its existing producer and final assembly. -/
theorem PreparedChosenModule.source_preExclusion_local_constrained_rows
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
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
          ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ CaseIComponentData.LocalConstrainedRows d K := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun _ hK hq hout hf =>
    d.localFamily_constrained_rows hG hempty hM hJ hu h hK hq hout hf⟩
end CFSG.Quasithin.Chapter15.Section01
