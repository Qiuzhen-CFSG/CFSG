module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenWeightTwo
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenPartition.Geometry

/-!
# Partition generation for the original ordinary A₇ block

Lift a three-pair partition containing the original Sylow image through
the prescribed L/O₂(L) marking. Its even stabilizer moves the weight-two
point defining M_L, so the preimage escapes M_L. Maximality of M_L then
gives generation of L by this preimage and M_L. The preimage is proper,
as the partition stabilizer has order 48 whereas A₇ has order 2520.

The argument applies to the full original local family, and the selected
component applications retain the original FF marking, both source primes
and the later exchanged selection. The extension SevenPartition.Membership establishes source-family
membership and placement in M, completing the A₇ alternative. Catalogue
exhaustion still requires the other branches.

Source: Aschbacher--Smith 15.1.20(2b) and 15.1.22(1), printed pp.1094--1099.
-/

public section
open Subgroup Equiv
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open AlternatingSeven.ThreeResidualLocals BinarySevenCode
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher ChapterC
open ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Full preimage of the partition stabilizer through the literal two-core quotient. -/
@[expose] def sevenPartitionPreimage (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (p : Partition 7 4 ![2,2,2,1]) : Subgroup G :=
  (p.stabilizer.comap ((alternatingGroup (Fin 7)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))))).map K.subtype

/-- Every three-pair preimage in the original local-family A₇ block is
proper, escapes the marked centralizer and generates the block with it. -/
theorem localFamily_seven_partition_generates (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ K)
    (hb : IsAlternatingBlock K 7)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (p : Partition 7 4 ![2,2,2,1]) :
      sevenPartitionPreimage K e p < K ∧
      ¬ sevenPartitionPreimage K e p ≤ d.MZ ⊓ K ∧
      sevenPartitionPreimage K e p ⊔ (d.MZ ⊓ K) = K := by
  obtain ⟨E,hE,u,hw,_,heq,hmax⟩ :=
    d.localFamily_seven_weight_two h hTM hu hK hi hb e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let f := (alternatingGroup (Fin 7)).subtype.comp q
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let P0 := p.stabilizer.comap f
  let P := P0.map K.subtype
  let C := (d.MZ ⊓ K).subgroupOf K
  have hPL : P ≤ K := map_subtype_le _
  have hproper : P ≠ K := by
    intro he
    have hle : alternatingGroup (Fin 7) ≤ p.stabilizer := by
      intro g hg
      obtain ⟨k,hk⟩ := hq ⟨g,hg⟩
      have hh : (k : G) ∈ P := he.symm ▸ k.property
      obtain ⟨l,hl,hlk⟩ := hh
      have hlk' : l = k := Subtype.ext hlk
      subst l
      change f k ∈ p.stabilizer at hl
      have hf : f k = g := congrArg Subtype.val hk
      exact hf ▸ hl
    have hh := Subgroup.card_le_of_le hle
    rw [nat_card_alternatingGroup,Nat.card_fin,SevenPartition.stabilizer_card] at hh
    norm_num at hh
  let w := BinarySevenCode.evenWordsEquivCore.symm (E u).toAdd
  have hw' : weight w.val = 2 := hw
  obtain ⟨g,hg,hmove⟩ := SevenPartition.partition_moves_weight_two p w hw'
  obtain ⟨k,hk⟩ := hq ⟨g,hg.1⟩
  have hkP : k ∈ P0 := by
    change f k ∈ p.stabilizer
    have hf : f k = g := congrArg Subtype.val hk
    exact hf.symm ▸ hg.2
  have hnot : ¬ P0 ≤ C := by
    intro hle
    have hkc0 : (k : G) ∈ d.MZ ⊓ K := hle hkP
    have hkc : (k : G) ∈ centralizer ({((u : K) : G)} : Set G) :=
      (heq ▸ hkc0).2
    have hku : blockConjugate K k u = u := by
      apply Subtype.ext
      apply Subtype.ext
      change (k : G) * ((u : K) : G) * (k : G)⁻¹ = ((u : K) : G)
      rw [mem_centralizer_singleton_iff.mp hkc,mul_inv_cancel_right]
    have hh := hE k u
    rw [hku] at hh
    apply hmove
    apply Subtype.ext
    have hf : f k = g := congrArg Subtype.val hk
    change f k = g at hf
    change (fun i => w.val (g.symm i)) = w.val
    change E u = BinaryPermutation.SevenMarkedAction.coreAction (f k) (E u) at hh
    rw [hf] at hh
    exact congrArg (fun v : Multiplicative (BinaryPermutation.core (Fin 7)) => v.toAdd.val) hh.symm
  have hgen : P0 ⊔ C = ⊤ := by
    exact hmax.lt_iff.mp (lt_of_le_not_ge le_sup_right (fun hh => hnot (le_sup_left.trans hh)))
  have hC : C.map K.subtype = d.MZ ⊓ K := map_subgroupOf_eq_of_le inf_le_right
  refine ⟨lt_of_le_of_ne hPL hproper,?_,?_⟩
  · intro hle
    exact hnot fun k hk => hle (mem_map_of_mem K.subtype hk)
  · have hh := congrArg (fun A : Subgroup K => A.map K.subtype) hgen
    rw [Subgroup.map_sup,hC,←MonoidHom.range_eq_map,K.range_subtype] at hh
    exact hh


/-- A partition over the original Sylow intersection inherits the general
escape and generation statements. -/
theorem localFamily_seven_partition_generation (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ K)
    (hb : IsAlternatingBlock K 7)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    ∃ p : Partition 7 4 ![2,2,2,1],
      d.S ⊓ K ≤ sevenPartitionPreimage K e p ∧
      sevenPartitionPreimage K e p < K ∧
      ¬ sevenPartitionPreimage K e p ≤ d.MZ ⊓ K ∧
      sevenPartitionPreimage K e p ⊔ (d.MZ ⊓ K) = K := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let f := (alternatingGroup (Fin 7)).subtype.comp q
  let R := (d.S ⊓ K).subgroupOf K
  have hR : IsPGroup 2 R :=
    (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)).comap_subtype
  obtain ⟨p,hp⟩ := SevenPartition.exists_partition (R.map f) (hR.map f)
  have hSL : d.S ⊓ K ≤ sevenPartitionPreimage K e p := by
    intro x hx
    exact ⟨⟨x,hx.2⟩,hp (mem_map_of_mem f hx),rfl⟩
  exact ⟨p,hSL,d.localFamily_seven_partition_generates h hTM hu hK hi hb e p⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher ChapterC
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Before prime exclusion, the actual marked A₇ quotient supplies a proper
three-pair preimage over S_L which escapes M_L and generates L with it. -/
theorem PreExclusionSource.constrained_seven_partition_generation
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7)) :
    IsAlternatingBlock d.L 7 ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
        (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
        ∃ π : Partition 7 4 ![2,2,2,1],
          d.SL ≤ sevenPartitionPreimage d.L t π ∧
          sevenPartitionPreimage d.L t π < d.L ∧
          ¬ sevenPartitionPreimage d.L t π ≤ d.ML ∧
          sevenPartitionPreimage d.L t π ⊔ d.ML = d.L := by
  obtain ⟨_,hi,_⟩ := s.constrained_small_alternating_input (h := h)
    hG hempty hM hJ hu hf (Or.inr rfl) e
  obtain ⟨hb,t,ht⟩ := s.constrained_seven_block (h := h) hG hempty hM hJ hu hf e
  exact ⟨hb,t,ht,d.localFamily_seven_partition_generation h hM.1.2 hu
    ⟨d.L_component.1,s.local_component⟩ hi hb t⟩

/-- The later exchanged selection retains the same original partition
preimage and its generation with the original marked centralizer. -/
theorem ExchangedSource.constrained_seven_partition_generation
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7)) :
    IsAlternatingBlock d.L 7 ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
        (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
        ∃ π : Partition 7 4 ![2,2,2,1],
          d.SL ≤ sevenPartitionPreimage d.L t π ∧
          sevenPartitionPreimage d.L t π < d.L ∧
          ¬ sevenPartitionPreimage d.L t π ≤ d.ML ∧
          sevenPartitionPreimage d.L t π ⊔ d.ML = d.L := by
  obtain ⟨_,hi,_⟩ := s.constrained_small_alternating_input hG hempty hM hJ hu h hf (Or.inr rfl) e
  obtain ⟨hb,t,ht⟩ := s.constrained_seven_block hG hempty hM hJ hu h hf e
  exact ⟨hb,t,ht,d.localFamily_seven_partition_generation h hM.1.2 hu
    ⟨d.L_component.1,s.local_component⟩ hi hb t⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher ChapterC
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual original marker supplies partition generation on the same
component and quotient, retaining original 15.1.14 as its explicit premise. -/
theorem PreparedChosenModule.source_preExclusion_constrained_seven_partition_generation
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
        ∀ e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7),
          IsAlternatingBlock d.L 7 ∧
          ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
            (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
            ∃ π : Partition 7 4 ![2,2,2,1],
              d.SL ≤ CaseIComponentData.sevenPartitionPreimage d.L t π ∧
              CaseIComponentData.sevenPartitionPreimage d.L t π < d.L ∧
              ¬ CaseIComponentData.sevenPartitionPreimage d.L t π ≤ d.ML ∧
              CaseIComponentData.sevenPartitionPreimage d.L t π ⊔ d.ML = d.L) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf e =>
    s.constrained_seven_partition_generation (h := h) hG hempty hM hJ hu hf e⟩

end CFSG.Quasithin.Chapter15.Section01
