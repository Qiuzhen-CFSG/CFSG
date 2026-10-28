module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSInputs
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCohomology

/-!
# Initial nonbinary MS classification inputs in the original nonblock configuration

Apply the intrinsic nonbinary reductions to Nonblock.msPair_of_quotient,
retaining c, the chosen module, the constrained hypothesis, the original
field size and the full quotient marking. The actual radical kernel and
FF action follow. The MS93 critical geometry is positive and even, its
edge-centralizer condition holds, and its core is the original Q c.

The whole initial moved space splits from its component-fixed complement
and is natural or doubled natural of the original field degree. The
central-omega centralizer is exactly the original two-core. At field four
the action component has full SL₃(4) order 60480.

The literal KR and KS two-cores agree. Thus the marked initial commutator
is the original movedCoreOmega, and its natural or doubled-natural section
model feeds the 4.3.9 centralizer argument. Only the original covector-parabolic
placement remains explicit in that application; its natural-module premise
is discharged here. The construction retains the given configuration, chosen
module and full quotient equivalence.
The full original Q now has its centralizer inside O₂(KR). In the abelian
branch, Q is elementary abelian and its faithful centralizer-quotient action
has an FF-offender. These applications discharge the exponent and offender
premises for whole-core reconstruction from the original MS3 condition.
Away from field four, the abelian whole core now centralizes the literal
intrinsic O₂(K), and the full supplied SL₃ quotient acts faithfully on it by
original conjugation. This discharges the component descent kernel; the
whole-module recognition and source radical inequalities remain open.
An actual natural whole-core section now gives a block on the original
c.K. In the nonblock branch, centrality of Q in O₂(KS), and in particular
abelianity of O₂(KS), therefore supplies a doubled-natural model on the
whole Q. That centrality is not asserted for arbitrary abelian Q.
The three nonblock module rows also compute the actual Sylow-omega
centralizer from the Sylow-fixed vectors in Q, Z(Q), or [Z(Q),K],
using every eligible Sylow overgroup of the original radical.
Without abelianity of Q, Z(Q) and [Z(Q),K] now have the original faithful
SL₃ action outside field four, and Z(Q) centralizes intrinsic O₂(K).
MS3 also supplies an FF action on the entire Ω₁(Z(Q)), including field four.
The original maximum elementary offenders now survive on both the whole
central omega and the initial layer. Their whole-action images escape the
two-core, and the whole central-omega and abelian-core offender groups contain
the full covering component, including at field four.

The general whole-core alternatives and Sylow radical inequalities of
C.1.34 and their selection in 4.3.8--10 remain to be proved.
The entire Q c/Φ(Q c) now has a kernel bound valid at field four and a
faithful fully generated SL₃ action outside field four. Its module recognition
remains open. Outside field four the whole Q c now equals the literal
intrinsic O₂(K c), with no abelianity premise. A strict difference between
these original subgroups forces the original field to have order four.

The original Sylow omega now splits on movedCoreOmega without whole-core
section premises. It is noncentral, and its radical comparison is equivalent
to the fixed-space core comparison in the faithful initial action.
The doubled initial branch now proves that strict radical inequality. Under
centrality of Q in O₂(KS), complete module alternatives follow. In the
original nonblock branch this supplies both the doubled whole-core model
and its required inequality; abelianity of O₂(KS) suffices, including at q=4.

Source: Aschbacher--Smith, original 4.3.8--10, pp.616--617, C.1.31--34,
pp.135--137; MS93 (2.2) and the opening of (3.2), pp.856--857,863.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterC.LinearThreeMS
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F]

/-- The original radical centralizes the original omega orbit exactly in O₂(KR). -/
theorem ms_omegaOrbit_radical_kernel
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    let J := K c ⊔ c.I.pCoreIn 2
    let R := (c.I.pCoreIn 2).subgroupOf J
    R ⊓ centralizer (MSCentralOrbit.omegaOrbit R : Set J) = pCore 2 J := by
  exact NonbinarySource.omegaOrbit_radical_kernel
    (msPair_of_quotient c D hf n (by omega) hF e) hn

/-- The FF action comes from the literal join, whose MS commutator is Q c. -/
theorem ms_core_and_centralOmega_isFF
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    let J := K c ⊔ c.I.pCoreIn 2
    msQ (K c) (c.I.pCoreIn 2) = Q c ∧
      Representation.BinaryOffender.IsFFModule
        (Representation.NormalElementaryQuotient.representation
          (Subgroup.omegaCenterIn (pCore 2 J))
          (QuotientGroup.mk' (centralizer (Subgroup.omegaCenterIn (pCore 2 J) : Set J)))
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) := by
  exact ⟨ms_commutator_eq c, NonbinarySource.centralOmega_isFF
    (msPair_of_quotient c D hf n (by omega) hF e) hn⟩

/-- The original configuration supplies the genuine critical geometry with core Q c. -/
theorem ms_critical_geometry
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    let J := K c ⊔ c.I.pCoreIn 2
    let R := (c.I.pCoreIn 2).subgroupOf J
    ∃ g : BinaryMS.MS93.Geometry R,
      0 < g.b R ∧ Even (g.b R) ∧ BinaryMS.MS93.EdgeCentralizerCondition R ∧
      ((BinaryMS.MS93.core R (BinaryMS.MS93.alpha R)).comap
        (Stellmacher.PushingUp.AmalgamGraph.embedM R)).map J.subtype = Q c := by
  let h := msPair_of_quotient c D hf n (by omega) hF e
  obtain ⟨g,hpos,heven⟩ := NonbinarySource.positive_even_geometry h hn
  exact ⟨g,hpos,heven,NonbinarySource.edge_centralizer h hn,
    (NonbinarySource.graph_core_pullback h hn).trans (ms_commutator_eq c)⟩

/-- The original nonblock omega-center action has the complete initial FF
natural/doubled-natural alternatives, with its original binary field degree. -/
theorem ms_initial_module_alternatives
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    let ρ := NonbinarySource.centralOmegaRepresentation (K c) (c.I.pCoreIn 2)
    let B := NonbinarySource.centralOmegaComponent (K c) (c.I.pCoreIn 2)
    let O := Representation.BinaryOffender.offenderSubgroup ρ
    ∃ d : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp O.subtype) (B.subgroupOf O),
    ∃ E : ChapterB.QuasisimpleSource.BinaryField, E.degree = n ∧
      (ChapterB.QuasisimpleSource.IsLinearNatural
        (d.sectionData.action.comp (B.subgroupOf O).subtype) E 3 ∨
      ChapterB.QuasisimpleSource.IsRepeatedLinearNatural
        (d.sectionData.space.toRepresentation.comp (B.subgroupOf O).subtype) E 3 2) := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact NonbinarySource.centralOmega_classified_source
    (msPair_of_quotient c D hf n (by omega) hF e) hn

/-- No odd scalar kernel is lost in the original nonblock omega-center action. -/
theorem ms_centralOmega_kernel
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    let J := K c ⊔ c.I.pCoreIn 2
    centralizer (Subgroup.omegaCenterIn (pCore 2 J) : Set J) = pCore 2 J := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact NonbinarySource.centralOmega_kernel_eq_core
    (msPair_of_quotient c D hf n (by omega) hF e) hn

/-- At field four the original initial component action has full SL₃(4)
order 60480, so the cubic scalar subgroup survives. -/
theorem ms_initial_component_card_four
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hF : Nat.card F = 4)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    Nat.card (NonbinarySource.centralOmegaComponent (K c) (c.I.pCoreIn 2)) = 60480 := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF' : Nat.card F = 2^2 := hF
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF')
  rw [NonbinarySource.centralOmegaComponent_card
    (msPair_of_quotient c D hf 2 (by decide) hF' e) (by decide),
    Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,hF]
  norm_num

/-- The original nonblock initial moved space splits from its fixed
complement and is natural or doubled natural in the original field degree. -/
theorem ms_initial_moved_space
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    let ρ := NonbinarySource.centralOmegaRepresentation (K c) (c.I.pCoreIn 2)
    let B := NonbinarySource.centralOmegaComponent (K c) (c.I.pCoreIn 2)
    let O := Representation.BinaryOffender.offenderSubgroup ρ
    ∃ d : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp O.subtype) (B.subgroupOf O),
    IsCompl d.sectionData.space.toSubmodule
      (Representation.BinaryOffender.fixedSpace (ρ.comp O.subtype) (B.subgroupOf O)) ∧
    ∃ E : ChapterB.QuasisimpleSource.BinaryField, E.degree = n ∧
      (ChapterB.QuasisimpleSource.IsLinearNatural
        (d.sectionData.space.toRepresentation.comp (B.subgroupOf O).subtype) E 3 ∨
      ChapterB.QuasisimpleSource.IsRepeatedLinearNatural
        (d.sectionData.space.toRepresentation.comp (B.subgroupOf O).subtype) E 3 2) := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact NonbinarySource.centralOmega_split_source
    (msPair_of_quotient c D hf n (by omega) hF e) hn

omit [Finite G] in
/-- The source placement of O₂(KS) in R identifies the original KR and KS
two-cores. Both containments use relative normality in the literal joins. -/
theorem ms_join_core_eq_sylow_join_core (c : SourceConfiguration T L) :
    (K c ⊔ c.I.pCoreIn 2).pCoreIn 2 = (K c ⊔ S c).pCoreIn 2 := by
  let J := K c ⊔ c.I.pCoreIn 2
  have hR : c.I.pCoreIn 2 ≤ S c := c.core_sylow.le.trans inf_le_left
  have hJS : J ≤ K c ⊔ S c := sup_le le_sup_left (hR.trans le_sup_right)
  have hSR : S c ≤ normalizer (c.I.pCoreIn 2 : Set G) := by
    rw [c.core_join]
    exact (le_sup_right : S c ≤ c.I ⊔ S c).trans
      ((c.I ⊔ S c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (c.I ⊔ S c)
          (pCore 2 (c.I ⊔ S c : Subgroup G))))
  have hSJ : S c ≤ normalizer (J : Set G) :=
    (le_inf (inf_le_right.trans c.normalizer_component.le) hSR).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply le_antisymm
  · exact pCoreIn_mono_of_normalizes hJS
      (sup_le ((le_sup_left : K c ≤ J).trans J.le_normalizer) hSJ)
  · exact (le_inf (c.block_join_core_le.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 hJS)

omit [Finite G] in
/-- The intrinsic MS initial omega group is the exact KS omega group used
by the original nonblock cohomology argument. -/
theorem ms_initialOmega_eq (c : SourceConfiguration T L) :
    NonbinarySource.initialOmega (K c) (c.I.pCoreIn 2) = coreOmega c := by
  rw [NonbinarySource.initialOmega_eq, ms_join_core_eq_sylow_join_core]

omit [Finite G] in
/-- The marked MS initial commutator is the original movedCoreOmega. -/
theorem ms_initialMoved_eq (c : SourceConfiguration T L) :
    NonbinarySource.initialMoved (K c) (c.I.pCoreIn 2) = movedCoreOmega c := by
  change ⁅NonbinarySource.initialOmega (K c) (c.I.pCoreIn 2),K c⁆ = _
  rw [ms_initialOmega_eq]

/-- The literal initial moved subgroup lies in the center U of the source Q. -/
theorem ms_initialMoved_le_center (c : SourceConfiguration T L) :
    movedCoreOmega c ≤ U c := by
  rw [← ms_initialMoved_eq]
  change NonbinarySource.initialMoved (K c) (c.I.pCoreIn 2) ≤
    Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (Q c)
  rw [← ms_commutator_eq]
  exact NonbinarySource.initialMoved_le_core_center

/-- The original nonblock moved omega has a natural or doubled-natural
section model over the given field, using one full SL₃ quotient marking. -/
theorem ms_initial_moved_section_models
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        (Representation.specialLinearNatural (k := F) 3) ∨
      HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        ((Representation.specialLinearNatural (k := F) 3).prod
          (Representation.specialLinearNatural (k := F) 3)) := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  simpa only [ms_initialMoved_eq] using NonbinarySource.initialMoved_section_models
    (msPair_of_quotient c D hf n (by omega) hF e) hn

/-- The source central omega splits over its actual moved subgroup. -/
theorem ms_initial_omega_split
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    movedCoreOmega c ⊔ (coreOmega c ⊓ centralizer (K c : Set G)) = coreOmega c ∧
    movedCoreOmega c ⊓ (coreOmega c ⊓ centralizer (K c : Set G)) = ⊥ := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  simpa only [ms_initialMoved_eq, ms_initialOmega_eq] using NonbinarySource.initialMoved_split
    (msPair_of_quotient c D hf n (by omega) hF e) hn

/-- Once the original parabolic is placed in these coordinates, its Sylow
centralizer is trivial. The natural-module premise is discharged here. -/
theorem ms_initial_mark_centralizer
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      (HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        (Representation.specialLinearNatural (k := F) 3) ∨
      HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor mark)
        ((Representation.specialLinearNatural (k := F) 3).prod
          (Representation.specialLinearNatural (k := F) 3))) ∧
      (Matrix.PSL3.LinearThree.lineLocalSL F ≤
          (L.subgroupOf (K c)).map (linearThreeActor mark) →
        S c ⊓ centralizer (K c : Set G) = ⊥ ∧
        msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥) := by
  obtain ⟨mark,hm⟩ := ms_initial_moved_section_models c D hf n hn hF e
  refine ⟨mark,hm,fun hL => ?_⟩
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
  have hc := sylow_centralizer_eq_bot_of_natural_omega c hf hlarge mark hm hL
  refine ⟨hc,bot_unique ?_⟩
  rw [ms_commutator_eq]
  exact (inf_le_inf_right _ (core_le_sylow c)).trans_eq hc


/-- In the original nonblock configuration, an abelian commutator core has
exponent two. This discharges the elementary-core premise of the whole-core
FF argument without assuming the C.1.34 classification. -/
theorem ms_core_elementary_of_abelian
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) (hc : IsMulCommutative (Q c)) :
    IsElementaryAbelian 2 (Q c) := by
  have hc' : IsMulCommutative (msQ (K c) (c.I.pCoreIn 2)) :=
    (ms_commutator_eq c).symm ▸ hc
  exact (ms_commutator_eq c) ▸ NonbinarySource.abelian_msQ_elementary
    (msPair_of_quotient c D hf n (by omega) hF e) hn hc'

/-- The full original Q has no centralizer outside the KR two-core.
This bound concerns Q itself, including the nonabelian branch. -/
theorem ms_core_centralizer_le
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    (K c ⊔ c.I.pCoreIn 2) ⊓ centralizer (Q c : Set G) ≤
      (K c ⊔ c.I.pCoreIn 2).pCoreIn 2 := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  simpa only [ms_commutator_eq] using NonbinarySource.msQ_centralizer_le_core
    (msPair_of_quotient c D hf n (by omega) hF e) hn

/-- MS3 yields an offender on the entire abelian Q in the original nonblock
configuration, with its literal join and centralizer quotient. -/
theorem ms_whole_core_isFF [CharP F 2]
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) (hc : IsMulCommutative (Q c)) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let hc' : IsMulCommutative (msQ (K c) (c.I.pCoreIn 2)) :=
      (ms_commutator_eq c).symm ▸ hc
    letI := NonbinarySource.component_normal hm hn
    letI := NonbinarySource.abelian_joinCore_elementary hm hn hc'
    Representation.BinaryOffender.IsFFModule
      (NonbinarySource.wholeCoreRepresentation hm hn hc') :=
  NonbinarySource.wholeCore_isFF
    (msPair_of_quotient c D hf n (by omega) hF e) hn
    ((ms_commutator_eq c).symm ▸ hc)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterC.LinearThreeMS Representation
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
/-- In the original configuration, centrality in O₂(KS) identifies the entire
source Q with the moved omega layer used in 4.3.9. -/
theorem ms_core_eq_initial_of_central
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hz : Q c ≤ centralizer ((K c ⊔ S c).pCoreIn 2 : Set G)) :
    Q c = movedCoreOmega c := by
  rw [←ms_commutator_eq,←ms_initialMoved_eq]
  apply NonbinarySource.msQ_eq_initialMoved_of_central
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  simpa only [ms_commutator_eq,ms_join_core_eq_sylow_join_core] using hz

/-- An actual natural whole-core section gives the block on the original
subgroup c.K of c.H, retaining its literal embedding. -/
theorem ms_block_of_natural_core
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      (specialLinearNatural (k := F) 3)) : IsBlock c.K := by
  have hm' : HasSectionModel (K c) (msQ (K c) (c.I.pCoreIn 2)) ⊥ (linearThreeActor e)
      (specialLinearNatural (k := F) 3) := (ms_commutator_eq c).symm ▸ hm
  have hs := NonbinarySource.short_of_natural_msQ
    (msPair_of_quotient c D hf n (by omega) hF e) hn e hm'
  let a : c.K ≃* K c := c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective
  exact ⟨inferInstance,hs.of_mulEquiv a.symm,c.component.subnormal⟩

/-- Under centrality of Q in the original KS two-core, the nonblock source
has a doubled natural whole core. No module classification is an input. -/
theorem ms_doubled_core_of_central
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ IsBlock c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hz : Q c ≤ centralizer ((K c ⊔ S c).pCoreIn 2 : Set G)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      HasSectionModel (K c) (Q c) ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)) := by
  have hz' : msQ (K c) (c.I.pCoreIn 2) ≤
      centralizer ((K c ⊔ c.I.pCoreIn 2).pCoreIn 2 : Set G) := by
    simpa only [ms_commutator_eq,ms_join_core_eq_sylow_join_core] using hz
  obtain ⟨mark,hm⟩ := NonbinarySource.msQ_section_models_of_central
    (msPair_of_quotient c D hf n (by omega) hF e) hn hz'
  rw [ms_commutator_eq] at hm
  rcases hm with hm | hm
  · exact (hb (ms_block_of_natural_core c D hf n hn hF mark hm)).elim
  · exact ⟨mark,hm⟩

/-- Abelianity of the literal KS two-core discharges centrality and supplies
the doubled whole-core input of the original nonblock argument. -/
theorem ms_doubled_core_of_abelian_joinCore
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ IsBlock c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hc : IsMulCommutative ((K c ⊔ S c).pCoreIn 2)) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      HasSectionModel (K c) (Q c) ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3)) := by
  apply ms_doubled_core_of_central c D hf hb n hn hF e
  apply le_trans _ (le_centralizer_iff_isMulCommutative.mpr hc)
  rw [←ms_commutator_eq,←ms_join_core_eq_sylow_join_core]
  exact NonbinarySource.msQ_le_joinCore

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Subgroup Theory.GroupTheory Representation
open ChapterC ChapterC.LinearThreeMS
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]

/-- The doubled section computes the centralizer in the original
KR, for every actual Sylow overgroup of its original radical. -/
theorem ms_doubled_sylow_centralizer
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P)
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e) ((specialLinearNatural (k := F) 3).prod (specialLinearNatural (k := F) 3))) :
    (K c ⊔ c.I.pCoreIn 2) ⊓ centralizer (SourceInterface.omegaCenterIn P : Set G) =
      (K c ⊓ centralizer ((Q c ⊓ centralizer (P : Set G) : Subgroup G) : Set G)) ⊔
        c.I.pCoreIn 2 := by
  simpa only [ms_commutator_eq, show SourceInterface.centerIn (Q c) = U c from rfl] using NonbinarySource.doubled_sylow_centralizer
    (msPair_of_quotient c D hf n (by omega) hF e) hn hP hRP e
    (by simpa only [ms_commutator_eq, show SourceInterface.centerIn (Q c) = U c from rfl] using hm)

/-- The natural center section computes the centralizer in the original
KR, for every actual Sylow overgroup of its original radical. -/
theorem ms_natural_center_sylow_centralizer
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P)
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e) (specialLinearNatural (k := F) 3)) :
    (K c ⊔ c.I.pCoreIn 2) ⊓ centralizer (SourceInterface.omegaCenterIn P : Set G) =
      (K c ⊓ centralizer ((U c ⊓ centralizer (P : Set G) : Subgroup G) : Set G)) ⊔
        c.I.pCoreIn 2 := by
  simpa only [ms_commutator_eq, show SourceInterface.centerIn (Q c) = U c from rfl] using NonbinarySource.natural_center_sylow_centralizer
    (msPair_of_quotient c D hf n (by omega) hF e) hn hP hRP e
    (by simpa only [ms_commutator_eq, show SourceInterface.centerIn (Q c) = U c from rfl] using hm)

/-- The natural center commutator section computes the centralizer in the original
KR, for every actual Sylow overgroup of its original radical. -/
theorem ms_natural_center_commutator_sylow_centralizer
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P)
    (hm : HasSectionModel (K c) (⁅U c,K c⁆) ⊥ (linearThreeActor e) (specialLinearNatural (k := F) 3)) :
    (K c ⊔ c.I.pCoreIn 2) ⊓ centralizer (SourceInterface.omegaCenterIn P : Set G) =
      (K c ⊓ centralizer ((⁅U c,K c⁆ ⊓ centralizer (P : Set G) : Subgroup G) : Set G)) ⊔
        c.I.pCoreIn 2 := by
  simpa only [ms_commutator_eq, show SourceInterface.centerIn (Q c) = U c from rfl] using NonbinarySource.natural_center_commutator_sylow_centralizer
    (msPair_of_quotient c D hf n (by omega) hF e) hn hP hRP e
    (by simpa only [ms_commutator_eq, show SourceInterface.centerIn (Q c) = U c from rfl] using hm)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterC.LinearThreeMS Representation
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open scoped MatrixGroups IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]

/-- In the original nonblock configuration away from field four, an abelian
Q centralizes the intrinsic component core. This discharges the kernel
premise for descending its entire component action. -/
theorem ms_abelian_core_centralizes_componentCore
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (h4 : n ≠ 2) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) (hc : IsMulCommutative (Q c)) :
    Q c ≤ centralizer ((K c).pCoreIn 2 : Set G) := by
  simpa only [ms_commutator_eq] using
    NonbinarySource.ComponentDescent.abelian_msQ_centralizes_componentCore
      (msPair_of_quotient c D hf n (by omega) hF e) hn h4
      ((ms_commutator_eq c).symm ▸ hc)

/-- The full original Q, with the supplied SL₃ marking, admits a faithful
action whose values on component representatives are literal conjugation.
No whole-section model or offender on this descended action is assumed. -/
theorem ms_abelian_core_descended_action
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (h4 : n ≠ 2) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) (hc : IsMulCommutative (Q c)) :
    ∃ a : SL(3,F) →* MulAut (Q c), Function.Injective a ∧
      ∀ (k : K c) (x : Q c), (a (linearThreeActor e k) x : G) =
        k * (x : G) * (k : G)⁻¹ := by
  obtain ⟨a,ha,he⟩ := NonbinarySource.ComponentDescent.exists_descendedAction
    (msPair_of_quotient c D hf n (by omega) hF e) hn h4 e
    ((ms_commutator_eq c).symm ▸ hc)
  let b : msQ (K c) (c.I.pCoreIn 2) ≃* Q c :=
    MulEquiv.subgroupCongr (ms_commutator_eq c)
  refine ⟨(MulAut.congr b).toMonoidHom.comp a,(MulAut.congr b).injective.comp ha,?_⟩
  intro k x
  exact he k (b.symm x)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterC.LinearThreeMS Representation
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]

/-- The actual whole center in the nonblock configuration centralizes
O₂(K), also when Q is nonabelian, outside field four. -/
theorem ms_center_centralizes_componentCore
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (h4 : n ≠ 2) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    SourceInterface.centerIn (Q c) ≤ centralizer ((K c).pCoreIn 2 : Set G) := by
  simpa only [ms_commutator_eq] using
    NonbinarySource.CentralSections.center_centralizes_componentCore
      (msPair_of_quotient c D hf n (by omega) hF e) hn h4

/-- The whole Z(Q) used in the third source row has the original faithful
SL₃ action; neither abelianity of Q nor a section model is assumed. -/
theorem ms_center_descended_action
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (h4 : n ≠ 2) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    ∃ a : SL(3,F) →* MulAut (SourceInterface.centerIn (Q c)), Function.Injective a ∧
      ∀ (k : K c) (x : SourceInterface.centerIn (Q c)),
        (a (linearThreeActor e k) x : G) = k * (x : G) * (k : G)⁻¹ := by
  obtain ⟨a,ha,he⟩ := NonbinarySource.CentralSections.exists_centerAction
    (msPair_of_quotient c D hf n (by omega) hF e) hn h4 e
  let b : SourceInterface.centerIn (msQ (K c) (c.I.pCoreIn 2)) ≃*
      SourceInterface.centerIn (Q c) :=
    MulEquiv.subgroupCongr (congrArg SourceInterface.centerIn (ms_commutator_eq c))
  exact ⟨(MulAut.congr b).toMonoidHom.comp a,(MulAut.congr b).injective.comp ha,
    fun k x => he k (b.symm x)⟩

omit [Finite G] in
private theorem faithful_conjugation_of_subgroup_eq
    {B : Type*} [Group B] {M X Y : Subgroup G}
    (actor : M →* B) (hXY : X = Y)
    (hX : ∃ a : B →* MulAut X, Function.Injective a ∧
      ∀ (k : M) (x : X), (a (actor k) x : G) = k * (x : G) * (k : G)⁻¹) :
    ∃ a : B →* MulAut Y, Function.Injective a ∧
      ∀ (k : M) (x : Y), (a (actor k) x : G) = k * (x : G) * (k : G)⁻¹ := by
  subst Y
  exact hX

/-- The fourth row's literal [Z(Q),K] inherits faithful descent with the
same original marking, without a recognition premise. -/
theorem ms_center_commutator_descended_action
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (h4 : n ≠ 2) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    ∃ a : SL(3,F) →* MulAut (⁅SourceInterface.centerIn (Q c),K c⁆ : Subgroup G),
      Function.Injective a ∧
      ∀ (k : K c) (x : (⁅SourceInterface.centerIn (Q c),K c⁆ : Subgroup G)),
        (a (linearThreeActor e k) x : G) = k * (x : G) * (k : G)⁻¹ := by
  exact faithful_conjugation_of_subgroup_eq (linearThreeActor e)
    (congrArg (fun H : Subgroup G => (⁅SourceInterface.centerIn H,K c⁆ : Subgroup G))
      (ms_commutator_eq c))
    (NonbinarySource.CentralSections.exists_centerCommutatorAction
      (msPair_of_quotient c D hf n (by omega) hF e) hn h4 e)


/-- At field four as well, the entire central omega of the original Q
has an FF action on its literal centralizer quotient. -/
theorem ms_coreOmega_isFF
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    letI := NonbinarySource.CentralSections.coreOmegaLayer_normal hm hn
    letI := NonbinarySource.CentralSections.coreOmegaLayer_elementary
      (K := K c) (R := c.I.pCoreIn 2)
    Representation.BinaryOffender.IsFFModule
      (NonbinarySource.CentralSections.coreOmegaRepresentation hm hn) :=
  NonbinarySource.CentralSections.coreOmega_isFF
    (msPair_of_quotient c D hf n (by omega) hF e) hn


/-- The original radical and each of its overgroups have a maximum elementary
subgroup offending on both the whole-core central omega and the initial layer.
Its whole-section image escapes the actual two-core, including at field four. -/
theorem ms_coreOmega_bestOffenders
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (P : Subgroup (K c ⊔ c.I.pCoreIn 2 : Subgroup G))
    (hRP : (c.I.pCoreIn 2).subgroupOf (K c ⊔ c.I.pCoreIn 2) ≤ P) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let E := NonbinarySource.CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := NonbinarySource.CentralSections.coreOmegaLayer_normal hm hn
    letI := NonbinarySource.CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    let q := QuotientGroup.mk' (centralizer (E : Set (K c ⊔ c.I.pCoreIn 2 : Subgroup G)))
    ∃ A ∈ Stellmacher.elementaryAbelianMaxSubgroups P,
      (¬ A ≤ pCore 2 (K c ⊔ c.I.pCoreIn 2 : Subgroup G)) ∧
      Representation.BinaryOffender.IsBestOffender
        (NonbinarySource.CentralSections.coreOmegaRepresentation hm hn) (A.map q) ∧
      (¬ A.map q ≤ pCore 2 ((K c ⊔ c.I.pCoreIn 2 : Subgroup G) ⧸ centralizer (E : Set (K c ⊔ c.I.pCoreIn 2 : Subgroup G)))) ∧
      Representation.BinaryOffender.IsBestOffender
        (NonbinarySource.centralOmegaRepresentation (K c) (c.I.pCoreIn 2))
        (A.map (NonbinarySource.centralOmegaProjection (K c) (c.I.pCoreIn 2))) :=
  NonbinarySource.NoncoreOffenders.coreOmega_bestOffenders
    (msPair_of_quotient c D hf n (by omega) hF e) hn P hRP

/-- The entire original component image belongs to the best-offender group
on the whole central omega, including field four and nonabelian Q. -/
theorem ms_coreOmega_component_le_offenders
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let E := NonbinarySource.CentralSections.coreOmegaLayer (K := K c) (R := c.I.pCoreIn 2)
    letI := NonbinarySource.CentralSections.coreOmegaLayer_normal hm hn
    letI := NonbinarySource.CentralSections.coreOmegaLayer_elementary (K := K c) (R := c.I.pCoreIn 2)
    ((K c).subgroupOf (K c ⊔ c.I.pCoreIn 2)).map
      (QuotientGroup.mk' (centralizer (E : Set (K c ⊔ c.I.pCoreIn 2 : Subgroup G)))) ≤
      Representation.BinaryOffender.offenderSubgroup
        (NonbinarySource.CentralSections.coreOmegaRepresentation hm hn) :=
  NonbinarySource.NoncoreOffenders.coreOmega_component_le_offenders
    (msPair_of_quotient c D hf n (by omega) hF e) hn

/-- In the abelian branch, the original whole-core offender group contains
the complete component image, also over the exceptional field four. -/
theorem ms_abelian_core_component_le_offenders
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hc : IsMulCommutative (Q c)) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    let hcomm : IsMulCommutative (msQ (K c) (c.I.pCoreIn 2)) := by rwa [ms_commutator_eq]
    let J := K c ⊔ c.I.pCoreIn 2
    let C := (⁅pCore 2 J,(K c).subgroupOf J⁆ : Subgroup J)
    letI := NonbinarySource.component_normal hm hn
    letI := NonbinarySource.abelian_joinCore_elementary hm hn hcomm
    ((K c).subgroupOf J).map (QuotientGroup.mk' (centralizer (C : Set J))) ≤
      Representation.BinaryOffender.offenderSubgroup (NonbinarySource.wholeCoreRepresentation hm hn hcomm) := by
  exact NonbinarySource.NoncoreOffenders.abelian_core_component_le_offenders
    (msPair_of_quotient c D hf n (by omega) hF e) hn (by rwa [ms_commutator_eq])

/-- The original nonblock Frattini section has no action kernel outside the
original two-core, including at field four. -/
theorem ms_frattini_action_kernel_le
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    let hm := msPair_of_quotient c D hf n (by omega) hF e
    (NonbinarySource.FrattiniSections.frattiniAction hm hn).ker ≤
      pCore 2 (K c ⊔ c.I.pCoreIn 2 : Subgroup G) :=
  NonbinarySource.FrattiniSections.frattiniAction_kernel_le
    (msPair_of_quotient c D hf n (by omega) hF e) hn

omit [Finite G] in
private theorem frattini_representation_congr
    {B : Type*} [Group B] {M X Y : Subgroup G}
    (actor : M →* B) (hXY : X = Y)
    (hX : IsElementaryAbelian 2 (X ⧸ frattini X))
    (hY : IsElementaryAbelian 2 (Y ⧸ frattini Y))
    (hr : letI := hX
      ∃ ρ : Representation (ZMod 2) B (Additive (X ⧸ frattini X)),
        Function.Injective ρ ∧
        (∀ (k : M) (x x' : X), (x' : G) = k * (x : G) * (k : G)⁻¹ →
          ρ (actor k) (Additive.ofMul (QuotientGroup.mk' (frattini X) x)) =
            Additive.ofMul (QuotientGroup.mk' (frattini X) x')) ∧
        Representation.BinaryOffender.subspaceCommutator ρ ⊤ ⊤ = ⊤) :
    letI := hY
    ∃ ρ : Representation (ZMod 2) B (Additive (Y ⧸ frattini Y)),
      Function.Injective ρ ∧
      (∀ (k : M) (x x' : Y), (x' : G) = k * (x : G) * (k : G)⁻¹ →
        ρ (actor k) (Additive.ofMul (QuotientGroup.mk' (frattini Y) x)) =
          Additive.ofMul (QuotientGroup.mk' (frattini Y) x')) ∧
      Representation.BinaryOffender.subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
  subst Y
  exact hr

/-- The actual original Q c modulo its Frattini subgroup has a faithful
marked SL₃ action with full displacement generation outside field four. -/
theorem ms_frattini_representation
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (h4 : n ≠ 2) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    letI : IsElementaryAbelian 2 (Q c ⧸ frattini (Q c)) := by
      exact (ms_commutator_eq c) ▸
        (NonbinarySource.FrattiniSections.frattini_elementary
          (K := K c) (R := c.I.pCoreIn 2))
    ∃ ρ : Representation (ZMod 2) SL(3,F) (Additive (Q c ⧸ frattini (Q c))),
      Function.Injective ρ ∧
      (∀ (k : K c) (x x' : Q c), (x' : G) = k * (x : G) * (k : G)⁻¹ →
        ρ (linearThreeActor e k) (Additive.ofMul (QuotientGroup.mk' (frattini (Q c)) x)) =
          Additive.ofMul (QuotientGroup.mk' (frattini (Q c)) x')) ∧
      Representation.BinaryOffender.subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
  exact frattini_representation_congr (linearThreeActor e) (ms_commutator_eq c)
    (NonbinarySource.FrattiniSections.frattini_elementary (K := K c) (R := c.I.pCoreIn 2))
    _ (NonbinarySource.FrattiniSections.exists_frattiniRepresentation
      (msPair_of_quotient c D hf n (by omega) hF e) hn h4 e)

/-- The original component core is trivial on Q c/Φ(Q c), even in the
nonabelian branch, outside field four. -/
theorem ms_componentCore_commutator_le_frattini
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (h4 : n ≠ 2) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    ⁅(K c).pCoreIn 2,Q c⁆ ≤ frattiniIn (Q c) := by
  simpa only [ms_commutator_eq] using
    NonbinarySource.FrattiniSections.componentCore_commutator_le_frattini
      (msPair_of_quotient c D hf n (by omega) hF e) hn h4

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterC.LinearThreeMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F]

/-- The original source Q is the whole intrinsic two-core outside field four,
including in the nonabelian rows. -/
theorem ms_core_eq_componentCore
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (h4 : n ≠ 2) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    Q c = (K c).pCoreIn 2 := by
  rw [←ms_commutator_eq c]
  exact NonbinarySource.IntrinsicCore.msQ_eq_componentCore
    (msPair_of_quotient c D hf n (by omega) hF e) hn h4

/-- A discrepancy between the original nonblock Q and O₂(K) can occur only
at the original field-four specialization. -/
theorem ms_degree_eq_two_of_core_ne
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hne : Q c ≠ (K c).pCoreIn 2) : n = 2 := by
  apply NonbinarySource.IntrinsicCore.degree_eq_two_of_core_ne
    (msPair_of_quotient c D hf n (by omega) hF e) hn
  simpa only [ms_commutator_eq] using hne

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterC ChapterC.LinearThreeMS
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F]

/-- The actual nonblock Sylow omega splits on the original movedCoreOmega,
without a model or abelianity premise on the whole Q. -/
theorem ms_sylowOmega_initial_split
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    SourceInterface.omegaCenterIn P =
      (movedCoreOmega c ⊓ centralizer (P : Set G)) ⊔
        SourceInterface.omegaCenterIn (K c ⊔ c.I.pCoreIn 2) ∧
    (movedCoreOmega c ⊓ centralizer (P : Set G)) ⊓
      SourceInterface.omegaCenterIn (K c ⊔ c.I.pCoreIn 2) = ⊥ := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  simpa only [ms_initialMoved_eq] using NonbinarySource.SylowInitial.sylowOmega_split_center
    (msPair_of_quotient c D hf n (by omega) hF e) hn hP hRP

/-- The original Sylow-omega centralizer is determined by movedCoreOmega
before the whole central or Frattini sections have been recognized. -/
theorem ms_initial_sylow_centralizer
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    (K c ⊔ c.I.pCoreIn 2) ⊓ centralizer (SourceInterface.omegaCenterIn P : Set G) =
      (K c ⊓ centralizer ((movedCoreOmega c ⊓ centralizer (P : Set G) : Subgroup G) : Set G)) ⊔
        c.I.pCoreIn 2 := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  simpa only [ms_initialMoved_eq] using NonbinarySource.SylowInitial.join_centralizer
    (msPair_of_quotient c D hf n (by omega) hF e) hn hP hRP

/-- The original nonbinary source excludes the central-Sylow-omega clause
of C.1.34(5), including at field four and with nonabelian Q. -/
theorem ms_sylowOmega_not_central
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2)) :
    ¬ SourceInterface.omegaCenterIn P ≤ SourceInterface.centerIn (K c ⊔ c.I.pCoreIn 2) := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact NonbinarySource.SylowInitial.sylowOmega_not_central
    (msPair_of_quotient c D hf n (by omega) hF e) hn hP

/-- The actual original radical inequality is equivalent to its literal
fixed-space comparison in the already classified faithful initial action. -/
theorem ms_radical_comparison_initial_action
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2)) :
    let J := K c ⊔ c.I.pCoreIn 2
    let q := NonbinarySource.centralOmegaProjection (K c) (c.I.pCoreIn 2)
    MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P ↔
      ((c.I.pCoreIn 2).subgroupOf J).map q ≠
        (Representation.NormalElementaryQuotient.fixedSpaceFixer
          (NonbinarySource.centralOmegaRepresentation (K c) (c.I.pCoreIn 2))
          ((P.subgroupOf J).map q)).pCoreIn 2 := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact NonbinarySource.SylowInitial.notCentralizerCore_iff_initial_action
    (msPair_of_quotient c D hf n (by omega) hF e) hn hP


/-- The original initial commutator has natural order, or every eligible
Sylow overgroup has the strict radical inequality required in C.1.34. -/
theorem ms_initial_order_or_radical_inequalities
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F)) :
    Nat.card (movedCoreOmega c) = 2^(3*n) ∨
      ∀ P : Subgroup G, Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2) →
        c.I.pCoreIn 2 ≤ P → MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  simpa only [ms_initialMoved_eq] using
    NonbinarySource.RadicalInitial.initial_order_or_radical_inequalities
      (msPair_of_quotient c D hf n (by omega) hF e) hn

/-- The actual original central-core branch now supplies complete C.1.34
alternatives, with no remaining module or radical-classification premise. -/
theorem ms_moduleAlternatives_of_central
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hz : Q c ≤ centralizer ((K c ⊔ S c).pCoreIn 2 : Set G))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F mark := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  apply NonbinarySource.RadicalInitial.moduleAlternatives_of_central
    (msPair_of_quotient c D hf n (by omega) hF e) hn _ hP hRP
  simpa only [ms_commutator_eq,ms_join_core_eq_sylow_join_core] using hz

/-- In the original nonblock branch, centrality in O₂(KS) supplies both
the whole doubled model and its actual Sylow radical inequality. -/
theorem ms_doubled_core_and_inequality_of_central
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ IsBlock c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hz : Q c ≤ centralizer ((K c ⊔ S c).pCoreIn 2 : Set G))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      HasSectionModel (K c) (Q c) ⊥ (linearThreeActor mark)
        ((Representation.specialLinearNatural (k := F) 3).prod (Representation.specialLinearNatural (k := F) 3)) ∧
      MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let h := msPair_of_quotient c D hf n (by omega) hF e
  have hz' : msQ (K c) (c.I.pCoreIn 2) ≤
      centralizer ((K c ⊔ c.I.pCoreIn 2).pCoreIn 2 : Set G) := by
    simpa only [ms_commutator_eq,ms_join_core_eq_sylow_join_core] using hz
  obtain ⟨mark,hm⟩ := ms_doubled_core_of_central c D hf hb n hn hF e hz
  refine ⟨mark,hm,?_⟩
  apply NonbinarySource.RadicalInitial.notCentralizerCore_of_initial_doubled h hn mark _ hP hRP
  have he := NonbinarySource.msQ_eq_initialMoved_of_central h hn hz'
  rw [←he,ms_commutator_eq]
  exact hm

/-- Abelianity of the literal KS two-core closes the original nonblock
doubled row, including its radical inequality at field four. -/
theorem ms_doubled_core_and_inequality_of_abelian_joinCore
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : ¬ IsBlock c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hc : IsMulCommutative ((K c ⊔ S c).pCoreIn 2))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      HasSectionModel (K c) (Q c) ⊥ (linearThreeActor mark)
        ((Representation.specialLinearNatural (k := F) 3).prod (Representation.specialLinearNatural (k := F) 3)) ∧
      MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P := by
  apply ms_doubled_core_and_inequality_of_central c D hf hb n hn hF e _ P hP hRP
  apply le_trans _ (le_centralizer_iff_isMulCommutative.mpr hc)
  rw [←ms_commutator_eq,←ms_join_core_eq_sylow_join_core]
  exact NonbinarySource.msQ_le_joinCore


/-- An actual doubled whole-core model supplies the literal Sylow radical
inequality in odd field degree, without centrality in O₂(KS). -/
theorem ms_radical_inequality_of_doubled
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3)))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  apply NonbinarySource.DoubledRadical.notCentralizerCore_of_doubled
    (msPair_of_quotient c D hf n (by omega) hF e) hn ho e _ hP hRP
  simpa only [ms_commutator_eq] using hm

/-- The original doubled whole-core row now supplies its full C.1.34
alternative in odd degree, with the supplied quotient marking retained. -/
theorem ms_moduleAlternatives_of_doubled
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3)))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F e := by
  apply Or.inr
  apply Or.inl
  exact ⟨by simpa only [ms_commutator_eq] using hm,
    ms_radical_inequality_of_doubled c D hf n hn ho hF e hm P hP hRP⟩

/-- An actual doubled whole-core model supplies the literal Sylow radical
inequality in every nonbinary field degree, without centrality in O₂(KS). -/
theorem ms_radical_inequality_of_doubled_all_degrees
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3)))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  apply NonbinarySource.DoubledRadical.notCentralizerCore_of_doubled_all_degrees
    (msPair_of_quotient c D hf n (by omega) hF e) hn e _ hP hRP
  simpa only [ms_commutator_eq] using hm

/-- The original doubled whole-core row now supplies its full C.1.34
alternative in every nonbinary degree, with the supplied quotient marking retained. -/
theorem ms_moduleAlternatives_of_doubled_all_degrees
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (Q c) ⊥ (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3)))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F e := by
  apply Or.inr
  apply Or.inl
  exact ⟨by simpa only [ms_commutator_eq] using hm,
    ms_radical_inequality_of_doubled_all_degrees c D hf n hn hF e hm P hP hRP⟩


/-- The original natural whole center is the already constructed initial
moved subgroup, including for the original field-four configuration. -/
theorem ms_natural_center_eq_movedCoreOmega
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3)) : U c = movedCoreOmega c := by
  have hm' : HasSectionModel (K c) (SourceInterface.centerIn (msQ (K c) (c.I.pCoreIn 2))) ⊥
      (linearThreeActor e) (Representation.specialLinearNatural (k := F) 3) := by
    simpa only [ms_commutator_eq,show SourceInterface.centerIn (Q c) = U c from rfl] using hm
  simpa only [ms_commutator_eq,ms_initialMoved_eq,
    show SourceInterface.centerIn (Q c) = U c from rfl] using
    NonbinarySource.NaturalCenter.center_eq_initial
      (msPair_of_quotient c D hf n (by omega) hF e) hn e hm'

/-- A natural whole moved center gives the entire original center's splitting
and removes the intrinsic component-core action, without a field-four exception. -/
theorem ms_natural_moved_center_structure
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) ⁅U c,K c⁆ ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3)) :
    ⁅U c,K c⁆ = movedCoreOmega c ∧
      U c ≤ centralizer ((K c).pCoreIn 2 : Set G) ∧
      ⁅U c,K c⁆ ⊔ (U c ⊓ centralizer (K c : Set G)) = U c ∧
      ⁅U c,K c⁆ ⊓ (U c ⊓ centralizer (K c : Set G)) = ⊥ := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let h := msPair_of_quotient c D hf n (by omega) hF e
  have hm' : HasSectionModel (K c) ⁅SourceInterface.centerIn (msQ (K c) (c.I.pCoreIn 2)),K c⁆ ⊥
      (linearThreeActor e) (Representation.specialLinearNatural (k := F) 3) := by
    simpa only [ms_commutator_eq,show SourceInterface.centerIn (Q c) = U c from rfl] using hm
  have he := NonbinarySource.NaturalCenter.centerCommutator_eq_initial h hn e hm'
  have hc := NonbinarySource.NaturalCenter.center_centralizes_componentCore h hn e hm'
  have hs := NonbinarySource.NaturalCenter.center_split h hn e hm'
  simpa only [ms_commutator_eq,ms_initialMoved_eq,
    show SourceInterface.centerIn (Q c) = U c from rfl] using (And.intro he (And.intro hc hs))

/-- The literal full center retains the supplied full SL₃ marking, including
at field four, once its whole moved center is natural. -/
theorem ms_natural_moved_center_action
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) ⁅U c,K c⁆ ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3)) :
    ∃ b : SL(3,F) →* MulAut (U c), Function.Injective b ∧
      ∀ (k : K c) (z : U c), (b (linearThreeActor e k) z : G) =
        k * (z : G) * (k : G)⁻¹ := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hm' : HasSectionModel (K c) ⁅SourceInterface.centerIn (msQ (K c) (c.I.pCoreIn 2)),K c⁆ ⊥
      (linearThreeActor e) (Representation.specialLinearNatural (k := F) 3) := by
    simpa only [ms_commutator_eq,show SourceInterface.centerIn (Q c) = U c from rfl] using hm
  exact faithful_conjugation_of_subgroup_eq (linearThreeActor e)
    (congrArg SourceInterface.centerIn (ms_commutator_eq c))
    (NonbinarySource.NaturalCenter.exists_centerAction
      (msPair_of_quotient c D hf n (by omega) hF e) hn e hm')


/-- The whole upper Frattini sections identify the original fixed factor as
all of C_Q(K). The splitting requires no ambient-centrality premise. -/
theorem ms_center_split_over_whole_fixed
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hU : HasSectionModel (K c) ⁅U c,K c⁆ ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hPhi : HasSectionModel (K c) (SourceInterface.frattiniIn (Q c)) (U c)
      (linearThreeActor e) (Representation.specialLinearNatural (k := F) 3).dual)
    (hD : HasSectionModel (K c)
      (Q c ⊓ centralizer (SourceInterface.frattiniIn (Q c) : Set G))
      (SourceInterface.frattiniIn (Q c)) (linearThreeActor e)
      ((Representation.specialLinearNatural (k := F) 3).dual.prod
        (Representation.specialLinearNatural (k := F) 3).dual))
    (hQ : HasSectionModel (K c) (Q c)
      (Q c ⊓ centralizer (SourceInterface.frattiniIn (Q c) : Set G))
      (linearThreeActor e) ((Representation.specialLinearNatural (k := F) 3).prod
        (Representation.specialLinearNatural (k := F) 3))) :
    Q c ⊓ centralizer (K c : Set G) = U c ⊓ centralizer (K c : Set G) ∧
      U c = (Q c ⊓ centralizer (K c : Set G)) ⊔ ⁅U c,K c⁆ ∧
      (Q c ⊓ centralizer (K c : Set G)) ⊓ ⁅U c,K c⁆ = ⊥ := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let h := msPair_of_quotient c D hf n (by omega) hF e
  have hu : SourceInterface.centerIn (Q c) = U c := rfl
  have hU' := hU
  have hPhi' := hPhi
  have hD' := hD
  have hQ' := hQ
  rw [←hu,←ms_commutator_eq c] at hU' hPhi'
  rw [←ms_commutator_eq c] at hD' hQ'
  simpa only [ms_commutator_eq,hu] using
    NonbinarySource.FixedCore.center_split_over_whole_fixed h hn e hU' hPhi' hD' hQ'

/-- In the literal line-parabolic configuration, a natural moved center is
already the entire natural center. The initial-module centralizer argument
kills the fixed factor; no fixed-factor order or ambient centrality is used. -/
theorem ms_natural_center_of_moved_and_line
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) ⁅U c,K c⁆ ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3))
    (hL : Matrix.PSL3.LinearThree.lineLocalSL F ≤
      (L.subgroupOf (K c)).map (linearThreeActor e)) :
    Q c ⊓ centralizer (K c : Set G) = ⊥ ∧
      HasSectionModel (K c) (U c) ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := F) 3) := by
  let := Fintype.ofFinite F
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have he := (ms_natural_moved_center_structure c D hf n hn hF e hm).1
  have hmodel : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
      (Representation.specialLinearNatural (k := F) 3) := he ▸ hm
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact_mod_cast Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hn
  have hSC := sylow_centralizer_eq_bot_of_natural_omega c hf hlarge e (Or.inl hmodel) hL
  have hCQ : Q c ⊓ centralizer (K c : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ (core_le_sylow c)).trans_eq hSC)
  refine ⟨hCQ,?_⟩
  have hm' : HasSectionModel (K c) ⁅SourceInterface.centerIn (msQ (K c) (c.I.pCoreIn 2)),K c⁆ ⊥
      (linearThreeActor e) (Representation.specialLinearNatural (k := F) 3) := by
    simpa only [ms_commutator_eq,show SourceInterface.centerIn (Q c) = U c from rfl] using hm
  have hCQ' : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using hCQ
  simpa only [ms_commutator_eq,show SourceInterface.centerIn (Q c) = U c from rfl] using
    NonbinarySource.FixedCore.natural_center_of_moved_of_fixed_eq_bot
      (msPair_of_quotient c D hf n (by omega) hF e) hn e hm' hCQ'

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
