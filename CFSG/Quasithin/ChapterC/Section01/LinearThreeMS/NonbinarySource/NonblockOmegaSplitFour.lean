module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.OmegaSplitFour
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# Field-four whole-section models in the original nonblock configuration

The original chosen module supplies C_Q(K)=1. Apply the intrinsic field-four
splitting theorem to its genuine MS-pair, retaining the constrained input,
full quotient marking, original commutator Q, radical and eligible Sylow
subgroups. The whole Ω₁(Z(Q)) is natural or doubled natural.

If Q is abelian, its complete C.1.34 alternatives follow. In the nonblock
branch the natural row contradicts the original block exclusion, leaving
an actual doubled whole-core model and the source strict radical inequality.
Neither abelianity of the ambient two-core nor an equivariant complement is
assumed. The nonabelian whole-center and upper/Frattini identification remains
with the intrinsic classification owner.

Source: Aschbacher–Smith C.1.34 and original 4.3.8–10, pp.136–137,616–617.
No Hypothesis1223 or new classification callback is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.OmegaSplitFour
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
open ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2^n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
include D hf hn hF e

/-- The original field-four nonblock input has a whole natural or doubled
central omega. The fixed-factor premise is supplied by its chosen module. -/
theorem source_omega_section_models (hfour : Nat.card F = 4) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      HasSectionModel (K c)
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c))
        ⊥ (linearThreeActor mark) (specialLinearNatural 3) ∨
      HasSectionModel (K c)
        (Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (Q c))
        ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) := by
  let hm := msPair_of_quotient c D hf n (by omega) hF e
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  simpa only [ms_commutator_eq] using
    ChapterC.LinearThreeMS.NonbinarySource.OmegaSplitFour.omega_section_models hm hn hfixed hfour

/-- Abelianity of the original Q suffices for C.1.34 at field four, with the
actual radical and every original eligible Sylow subgroup. -/
theorem source_moduleAlternatives_of_abelian (hfour : Nat.card F = 4)
    (hc : IsMulCommutative (Q c))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      MSModuleAlternatives (K c) (c.I.pCoreIn 2) P n F mark := by
  let hm := msPair_of_quotient c D hf n (by omega) hF e
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  exact ChapterC.LinearThreeMS.NonbinarySource.OmegaSplitFour.moduleAlternatives_of_abelian
    hm hn hfixed hfour ((ms_commutator_eq c).symm ▸ hc) hP hRP

/-- In the actual nonblock branch an abelian Q is doubled natural and has the
source strict radical inequality. No ambient-core abelianity is required. -/
theorem source_doubled_and_inequality_of_abelian (hfour : Nat.card F = 4)
    (hb : ¬ IsBlock c.K) (hc : IsMulCommutative (Q c))
    (P : Subgroup G) (hP : Chapter1.IsSylowIn 2 P (K c ⊔ c.I.pCoreIn 2))
    (hRP : c.I.pCoreIn 2 ≤ P) :
    ∃ mark : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F),
      HasSectionModel (K c) (Q c) ⊥ (linearThreeActor mark)
        ((specialLinearNatural (k := F) 3).prod (specialLinearNatural 3)) ∧
      MSNotCentralizerCore (K c) (c.I.pCoreIn 2) P := by
  let hm := msPair_of_quotient c D hf n (by omega) hF e
  have hfixed : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  obtain ⟨mark,hm | hm⟩ :=
    ChapterC.LinearThreeMS.NonbinarySource.OmegaSplitFour.abelian_section_models
      hm hn hfixed hfour ((ms_commutator_eq c).symm ▸ hc)
  · rw [ms_commutator_eq] at hm
    exact (hb (ms_block_of_natural_core c D hf n hn hF mark hm)).elim
  · refine ⟨mark,?_,DoubledRadical.notCentralizerCore_of_doubled_all_degrees
      (msPair_of_quotient c D hf n (by omega) hF e) hn mark hm hP hRP⟩
    simpa only [ms_commutator_eq] using hm

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.OmegaSplitFour
