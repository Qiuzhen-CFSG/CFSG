module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.G2MarkedGeometry
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.Source

/-!
# Original constrained local rows and their full source refinement

The original local-family classification is combined with the reconstructed
blocks precisely in the additional C-component branch of 15.1.20(2b).
The rank-two blocks have both literal maximal centralizers; the seven-point
block has its weight-two vector in the full U(K). The binary-linear rows
retain both actual flag parabolics. No general local member is promoted to
an ambient C-component, and no new Sylow-normalization premise is imposed.

For the selected component, the source-correct rank-one exclusion removes
the first row. The remaining alternatives are refined with the A₇ partition
and weight-two marking, the opposite A₆/G₂ parabolics under one quotient
marking, and the literal residual-centralizer identities. The original
marker is constructed once for both results; later exchanged selection
uses that same source. All public predecessor interfaces remain available.

These assembly theorems retain the independently owned whole-core A₆
reconstruction and original 15.1.14 residual as explicit inputs. They do
not discharge those inputs or claim unconditional seven-row exhaustion.
The ordinary source rows retain their separate producer and full-catalogue
assembly owner. The exact FF and core-to-star comparisons used by the
block constructions remain those of the imported original local-family APIs.

Source: Aschbacher--Smith 15.1.20(1)--(2) and 15.1.22(1)--(3),
printed pp.1094--1100, refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

private theorem image_model_of_centerless_core
    {d : CaseIComponentData T M Mc V} {K : Subgroup G}
    (a : d.NormalizerAction K) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    {Y : Type*} [Group Y] (e : (K ⧸ pCore 2 K) ≃* Y) (hz : center Y = ⊥) :
    Nonempty (d.normalizerImage K ≃* Y) := by
  have hZ : center (K ⧸ pCore 2 K) = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [FixedElementary.map_center,hz,Subgroup.map_bot]
  have hi : Function.Injective a.coreToImage :=
    (MonoidHom.ker_eq_bot_iff a.coreToImage).mp (bot_unique ((a.coreToImage_ker_central hq).trans_eq hZ))
  exact ⟨(MulEquiv.ofBijective a.coreToImage ⟨hi,a.coreToImage_surjective⟩).symm.trans e⟩

/-- The extra block and geometric clauses in 15.1.20(2), only for actual
C-components. The seven-point action is on the whole original U(K). -/
inductive LocalComponentSourceGeometry (d : CaseIComponentData T M Mc V) (K : Subgroup G) : Prop
  | alternatingFive (block : IsAlternatingBlock K 5)
      (borel : d.MZ ⊓ K = d.localSylowBorel K)
  | seven (block : IsAlternatingBlock K 7)
      (t : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
      (E : blockU K ≃* Multiplicative (BinaryPermutation.core (Fin 7)))
      (action : ∀ k u, E (blockConjugate K k u) =
        BinaryPermutation.SevenMarkedAction.coreAction
          (t (QuotientGroup.mk' (pCore 2 K) k)).val (E u))
      (u : blockU K) (weight : BinarySevenCode.weight (E u).toAdd.val = 2)
      (fixed : ((u : K) : G) ∈ centralizer (d.normalizerSylow K : Set G))
      (centralizer : d.MZ ⊓ K = K ⊓ Subgroup.centralizer ({((u : K) : G)} : Set G))
      (maximal : IsCoatom ((d.MZ ⊓ K).subgroupOf K))
  | rankTwo (block : IsSL3EvenBlock K 1 ∨ IsAlternatingBlock K 6 ∨ ChapterC.IsG2TwoBlock K)
      (seed : d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G))
      (maximal : IsCoatom ((d.MZ ⊓ K).subgroupOf K))
      (fixed : d.MZ ⊓ K = K ⊓ centralizer
        (((blockU K).map K.subtype ⊓ centralizer (d.S ⊓ K : Set G) : Subgroup G) : Set G))
  | linear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (t : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
      (marked : d.MZ ⊓ K < K ∧ LocalLinearParabolic t (d.MZ ⊓ K))
      (selected : M ⊓ K < K ∧ LocalLinearParabolic t (M ⊓ K))

/-- The full additional geometry in the actual C-component branch. Both
six-point covering outcomes pass through the original reconstruction and exclusion. -/
theorem PreExclusionSource.localComponent_source_geometry
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hc : K ∈ Chapter1.cComponentsIn d.G1)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) : LocalComponentSourceGeometry d K := by
  obtain ⟨_,_,hb⟩ := s.localComponent_block_rows (h := h) hp ha hG hempty hM hJ hu
    hne hmany hfull hres hK hc hq hout hf
  rcases hb with hb | hb | hb | hb | hb | ⟨n,hn,⟨t⟩⟩
  · exact .alternatingFive hb ((d.localFamily_alternatingFive_borel h hM.1.2 hu hK hq hout hb).2.trans
      (d.localSylowBorel_eq K).symm)
  · obtain ⟨_,⟨m⟩,_⟩ := hb.2.2
    have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
    obtain ⟨e⟩ := image_model_of_centerless_core a hq m.quotientIso
      (alternatingGroup.center_eq_bot (by simp))
    obtain ⟨hb,t,_,E,hE,u,hw,hfix,hcent,hmax⟩ :=
      s.localComponent_seven (h := h) hG hempty hM hJ hu hK hc hq hout hf e
    exact .seven hb t E hE u hw hfix hcent hmax
  · obtain ⟨hs,hm,hf⟩ := d.localFamily_binaryThree_seed_centralizer h hM.1.2 hu hK hq hout hb
    exact .rankTwo (Or.inl hb) hs hm hf
  · obtain ⟨hs,hm,hf⟩ := d.localFamily_six_seed_centralizer h hM.1.2 hu hK hq hout hb
    exact .rankTwo (Or.inr (Or.inl hb)) hs hm hf
  · obtain ⟨hs,hm,hf⟩ := d.localFamily_g2_seed_centralizer h hM.1.2 hu hK hq hout hb
    exact .rankTwo (Or.inr (Or.inr hb)) hs hm hf
  · have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
    obtain ⟨e⟩ := image_model_of_centerless_core a hq t
      (_root_.BinaryLinear.OuterCyclic.binary_center_eq_bot (by omega))
    obtain ⟨t,_,hmarked,hselected⟩ :=
      d.localFamily_binary_linear_marked_parabolics hG hempty hM hJ hu h hK hq hout hf hn e
    exact .linear n hn t hmarked hselected

/-- Original 15.1.20(1)--(2) for every eligible member of the original local
family. Only the source's additional block clause asks for C-componenthood. -/
theorem PreExclusionSource.localFamily_source20
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    Chapter1.IsSylowIn 2 (d.S ⊓ K) K ∧ ¬ K ≤ M ∧
      ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ LocalConstrainedSourceRows d K ∧
      (K ∈ Chapter1.cComponentsIn d.G1 → LocalComponentSourceGeometry d K) := by
  obtain ⟨hm,hr⟩ := s.localFamily_constrained_source_rows (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hf
  exact ⟨ComponentModels.source20_sylow_intersection hK.2,
    d.localFamily_not_le_M hG hempty hM hu hK hout,hm,hr,
    fun hc => s.localComponent_source_geometry (h := h) hp ha
      hG hempty hM hJ hu hne hmany hfull hres hK hc hq hout hf⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Theory.SpecificGroups.SymmetricSix Atlas.G2.BinaryParabolicPair
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- The full common geometry of source 15.1.22(2), including the full U(L)
centralizer and the literal O^{3′} residual centralizer. -/
structure ConstrainedRankTwoSourceGeometry (d : CaseIComponentData T M Mc V) : Prop where
  sylow : Chapter1.IsSylowIn 2 d.SL d.L
  marked_sylow : d.SL ≤ d.ML
  selected_sylow : d.SL ≤ M ⊓ d.L
  seed : d.ML = d.L ⊓ centralizer (centralInvolutions T : Set G)
  fixed : d.ML = d.L ⊓ centralizer
    (((blockU d.L).map d.L.subtype ⊓ centralizer (d.SL : Set G) : Subgroup G) : Set G)
  marked_maximal : IsCoatom (d.ML.subgroupOf d.L)
  selected_maximal : IsCoatom ((M ⊓ d.L).subgroupOf d.L)
  distinct : d.ML ≠ M ⊓ d.L
  marked_source : d.IsSourceParabolic d.ML
  selected_source : d.IsSourceParabolic (M ⊓ d.L)
  generated : (M ⊓ d.L) ⊔ d.ML = d.L
  centralizers : d.ConstrainedCentralizerIdentity

/-- The constrained rows of original 15.1.22. Each row keeps its extra
source clauses and actual model maps, beyond the weaker exclusion interface. -/
inductive ConstrainedSource22Alternatives (d : CaseIComponentData T M Mc V) : Prop
  | seven (base : d.ConstrainedA7Alternative) (proper : M ⊓ d.L < d.L)
      (t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7))
      (π : Partition 7 4 ![2,2,2,1])
      (parabolic : d.IsSourceParabolic (sevenPartitionPreimage d.L t π))
      (sylow : d.SL ≤ sevenPartitionPreimage d.L t π)
      (placement : sevenPartitionPreimage d.L t π ≤ M ⊓ d.L)
      (E : blockU d.L ≃* Multiplicative (BinaryPermutation.core (Fin 7)))
      (action : ∀ k u, E (blockConjugate d.L k u) =
        BinaryPermutation.SevenMarkedAction.coreAction
          (t (QuotientGroup.mk' (pCore 2 d.L) k)).val (E u))
      (u : blockU d.L) (weight : BinarySevenCode.weight (E u).toAdd.val = 2)
      (fixed : ((u : d.L) : G) ∈ centralizer (d.normalizerSylow d.L : Set G))
      (centralizer : d.ML = d.L ⊓ Subgroup.centralizer ({((u : d.L) : G)} : Set G))
      (maximal : IsCoatom (d.ML.subgroupOf d.L))
  | linearThree (base : d.ConstrainedL3Alternative)
      (geometry : d.ConstrainedRankTwoSourceGeometry)
      (t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL)
      (marked : d.ConstrainedLinearParabolic t d.ML)
      (selected : d.ConstrainedLinearParabolic t (M ⊓ d.L))
  | six (block : IsAlternatingBlock d.L 6)
      (geometry : d.ConstrainedRankTwoSourceGeometry)
      (t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 6))
      (g : alternatingGroup (Fin 6))
      (marking :
        let q := t.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
        (((d.ML.subgroupOf d.L).map q = (MulAut.conj g).mapSubgroup a6DuadStabilizer ∧
          ((M ⊓ d.L).subgroupOf d.L).map q = (MulAut.conj g).mapSubgroup a6SynthemeStabilizer) ∨
         ((d.ML.subgroupOf d.L).map q = (MulAut.conj g).mapSubgroup a6SynthemeStabilizer ∧
          ((M ⊓ d.L).subgroupOf d.L).map q = (MulAut.conj g).mapSubgroup a6DuadStabilizer)))
  | g2 (block : ChapterC.IsG2TwoBlock d.L)
      (geometry : d.ConstrainedRankTwoSourceGeometry)
      (t : (d.L ⧸ pCore 2 d.L) ≃* DerivedModel) (g : DerivedModel)
      (marking :
        let q := (MulAut.conj g).toMonoidHom.comp
          (t.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))
        (((d.ML.subgroupOf d.L).map q = derivedFirst ∧
          ((M ⊓ d.L).subgroupOf d.L).map q = derivedSecond) ∨
         ((d.ML.subgroupOf d.L).map q = derivedSecond ∧
          ((M ⊓ d.L).subgroupOf d.L).map q = derivedFirst)))
  | linear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (fitting : generalizedFitting d.L = pCore 2 d.L)
      (t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
      (marked : d.ConstrainedLinearParabolic t d.ML)
      (selected : d.ConstrainedLinearParabolic t (M ⊓ d.L))
      (generated : (M ⊓ d.L) ⊔ d.ML = d.L)
      (marked_proper : d.ML < d.L) (selected_proper : M ⊓ d.L < d.L)

/-- The entire constrained refinement of original 15.1.22, at either source
prime. The independent earlier residual and whole-core A₆ reconstruction
are the only unproved external mathematics retained by this assembly. -/
theorem PreExclusionSource.constrained_source22
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (thompsonFixed T V : Set G))
    (hf : generalizedFitting d.L = pCore 2 d.L) : d.ConstrainedSource22Alternatives := by
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h
    hK s.quasisimple d.L_not_le_MZ hf
  have hall := s.constrained_catalogue_of_reconstruction (h := h) ha
    hG hempty hM hJ hu hne hmany hfull hres hf
  have hloc := s.local_intersections (h := h) hG hu hM.1.2
  cases hall with
  | rankOne r => exact (s.no_constrained_rankOne (h := h) hp hG hM hJ r).elim
  | linearThree r =>
    obtain ⟨F,_,_,hF,ρ,⟨m⟩,_⟩ := r.block.2.2
    let _ := Fintype.ofFinite F
    have hfield : Fintype.card F = 2 := by simpa only [←Nat.card_eq_fintype_card,pow_one] using hF
    let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hfield).symm
    obtain ⟨e⟩ := image_model_of_centerless_core a s.quasisimple
      (m.quotientIso.trans (Atlas.fieldEquivSL 3 eF))
      (_root_.BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide))
    obtain ⟨t,_,hm,hn,i,hP,hR,hpos⟩ := s.constrained_binaryThree_source_parabolics (h := h)
      hG hempty hM hJ hu hf e
    obtain ⟨hseed,hmax,hfixed⟩ := d.localFamily_binaryThree_seed_centralizer h hM.1.2 hu
      hK s.quasisimple d.L_not_le_MZ r.block
    have hother : IsCoatom ((M ⊓ d.L).subgroupOf d.L) ∧
        d.IsSourceParabolic d.ML ∧ d.IsSourceParabolic (M ⊓ d.L) ∧
        (M ⊓ d.L) ⊔ d.ML = d.L := by
      rcases hpos with ⟨hl,hr⟩ | ⟨hl,hr⟩
      · exact ⟨hr.symm ▸ i.right_maximal,hl.symm ▸ hP,hr.symm ▸ hR,
          by rw [hl,hr,sup_comm,i.generated]⟩
      · exact ⟨hr.symm ▸ i.left_maximal,hl.symm ▸ hR,hr.symm ▸ hP,
          by rw [hl,hr,i.generated]⟩
    exact .linearThree r
      ⟨s.component_sylow,hloc.2.1,hloc.2.2.2.1,
        hseed,hfixed,hmax,hother.1,r.distinct,hother.2.1,hother.2.2.1,
        hother.2.2.2,r.centralizers⟩ t hm hn
  | alternatingSeven r =>
    obtain ⟨_,⟨m⟩,_⟩ := r.block.2.2
    obtain ⟨e⟩ := image_model_of_centerless_core a s.quasisimple m.quotientIso
      (alternatingGroup.center_eq_bot (by simp))
    obtain ⟨t,_,π,hP,hSL,hplace,hproper,r',_⟩ :=
      s.constrained_seven (h := h) hG hempty hM hJ hu hf e
    obtain ⟨_,hi,_⟩ := s.constrained_small_alternating_input (h := h)
      hG hempty hM hJ hu hf (Or.inr rfl) e
    obtain ⟨E,hE,u,hw,hfix,hcent,hmax⟩ :=
      d.localFamily_seven_weight_two h hM.1.2 hu hK hi r'.block t
    exact .seven r' hproper t π hP hSL hplace E hE u hw hfix hcent hmax
  | alternatingSix hb _ =>
    obtain ⟨_,hseed,hmax,hmax',hne,hgen,hP,hR,_,hcent,_⟩ :=
      s.constrained_six_of_block (h := h) hG hempty hM hJ hu hfull hb
    obtain ⟨_,_,hfixed⟩ := d.localFamily_six_seed_centralizer h hM.1.2 hu
      hK s.quasisimple d.L_not_le_MZ hb
    obtain ⟨_,⟨m⟩,_⟩ := hb.2.2
    obtain ⟨g,hmark⟩ := s.constrained_six_marked_parabolics (h := h)
      hG hempty hM hJ hu hfull hb m.quotientIso
    exact .six hb ⟨s.component_sylow,hloc.2.1,hloc.2.2.2.1,
      hseed,hfixed,hmax,hmax',hne,hP,hR,hgen,hcent⟩ m.quotientIso g hmark
  | g2 hb hcent =>
    obtain ⟨t⟩ := hb.quotient_iso
    obtain ⟨e⟩ := image_model_of_centerless_core a s.quasisimple t
      Theory.SpecificGroups.g2_derived_two_center_eq_bot
    obtain ⟨t,_,g,hmark,hP,hR,hmax,hmax',hne,hgen⟩ :=
      s.constrained_g2_marked_parabolics (h := h) hG hempty hM hJ hu hf e
    obtain ⟨hseed,_,hfixed⟩ := d.localFamily_g2_seed_centralizer h hM.1.2 hu
      hK s.quasisimple d.L_not_le_MZ hb
    exact .g2 hb ⟨s.component_sylow,hloc.2.1,hloc.2.2.2.1,
      hseed,hfixed,hmax,hmax',hne,hP,hR,hgen,hcent⟩ t g hmark
  | linear n hn t hm hn' hg =>
    exact .linear n hn hf t hm hn' hg hloc.2.2.1 hloc.2.2.2.2.1

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original-marker assembly of all constrained 15.1.20(2) local-family
clauses and the constrained 15.1.22 refinement. The marker is chosen once;
all applications retain its G₁,M_Z,S,Q₁ and literal quotient maps. -/
theorem PreparedChosenModule.source_preExclusion_constrained_source20_source22
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized) (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
          Chapter1.IsSylowIn 2 (d.S ⊓ K) K ∧ ¬ K ≤ M ∧
          ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧ CaseIComponentData.LocalConstrainedSourceRows d K ∧
          (K ∈ Chapter1.cComponentsIn d.G1 → CaseIComponentData.LocalComponentSourceGeometry d K)) ∧
      (generalizedFitting d.L = pCore 2 d.L →
        d.ConstrainedAlternatives ∧ d.ConstrainedSource22Alternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_,?_⟩
  · intro K hK hq hout hf
    exact s.localFamily_source20 (h := h) hp ha
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hf
  · intro hf
    exact ⟨s.constrained_catalogue_of_reconstruction (h := h) ha
      hG hempty hM hJ hu hne hmany hfull hres hf,
      s.constrained_source22 (h := h) hp ha hG hempty hM hJ hu hne hmany hfull hres hf⟩

namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The later exchanged application retains the same source refinement and
all additional geometry, with no use of exchanged selection in prime-five proofs. -/
theorem ExchangedSource.constrained_source20_source22
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (x : d.ExchangedSource) (s : d.PreExclusionSource h.normalized 3)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤ centralizer (thompsonFixed T V : Set G))
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    Chapter1.IsSylowIn 2 d.SL d.L ∧ ¬ d.L ≤ M ∧
      ⁅d.L,elementaryAbelianMaxJ d.S⁆ = d.L ∧ LocalConstrainedSourceRows d d.L ∧
      LocalComponentSourceGeometry d d.L ∧ d.ConstrainedSource22Alternatives := by
  obtain ⟨hs,hout,hm,hr,hc⟩ := s.localFamily_source20 (h := h) (Or.inl rfl) ha
    hG hempty hM hJ hu hne hmany hfull hres
    ⟨d.L_component.1,x.local_component⟩ x.quasisimple d.L_not_le_MZ hf
  exact ⟨hs,hout,hm,hr,hc d.L_component,
    s.constrained_source22 (h := h) (Or.inl rfl) ha hG hempty hM hJ hu hne hmany hfull hres hf⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
