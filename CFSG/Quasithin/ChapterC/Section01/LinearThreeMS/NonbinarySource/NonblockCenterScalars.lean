module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.InitialDetection
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.NonblockInitialFixed

/-!
# Scalar actions on the whole original nonblock center

The actual initial alternatives supply C_Q(K)=1 in the original configuration.
Apply the intrinsic detection theorem to the whole U=Z(Q), retaining the given
full SL₃ quotient marking. Every nonidentity scalar fixes no element of U other
than the identity. Odd-order extraction in the original component gives an
actual element of order three inducing any prescribed nonidentity scalar.
In particular the field-four configuration supplies such a cubic element
and proves [U,K]=U on the whole center, without a whole-center, Frattini-section, or ambient-centrality premise.

These are whole-center action facts for the recognition step in original
4.3.8--10. They neither identify the whole sections nor eliminate the remaining
even covering kernels. Source: Aschbacher--Smith C.1.34, pp.136--137,
and original 4.3.8--10, pp.616--617.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.CenterScalars
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.LinearThreeMS.NonbinarySource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
  (hf : generalizedFitting c.K = pCore 2 c.K)
  (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
  (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))

include D hf n hn hF in
/-- Scalar fixation is excluded on the entire original U, for the supplied
marking and without any whole-section model. -/
theorem source_center_scalar_fixed_eq_bot (k : K c)
    (hk : linearThreeActor e k ∈ center SL(3,F))
    (hne : linearThreeActor e k ≠ 1) :
    U c ⊓ centralizer ({(k : G)} : Set G) = ⊥ := by
  have hfix := (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  have hpair := msPair_of_quotient c D hf n (by omega) hF e
  have hfix' : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using hfix
  simpa only [ms_commutator_eq,
    show Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (Q c) = U c from rfl] using
    InitialDetection.center_scalar_fixed_eq_bot_of_no_fixed_factor hpair hn hfix' e k hk hne

include D hf n hn hF in
/-- Any prescribed nontrivial scalar has an actual cubic lift in the original
component, acting fixed-freely on the same whole U. -/
theorem source_cubic_scalar_lift (s : SL(3,F))
    (hs : s ∈ center SL(3,F)) (hne : s ≠ 1) :
    ∃ k : K c, linearThreeActor e k = s ∧ orderOf (k : G) = 3 ∧
      U c ⊓ centralizer ({(k : G)} : Set G) = ⊥ := by
  have hfix := (InitialFixed.source_fixed_factors D hf hn hF e).2.1
  have hpair := msPair_of_quotient c D hf n (by omega) hF e
  have hfix' : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using hfix
  obtain ⟨k,hk,ho,hfree⟩ :=
    InitialDetection.exists_cubic_scalar_lift hpair hn hfix' e s hs hne
  refine ⟨k,hk,?_,?_⟩
  · simpa only [Subgroup.orderOf_coe] using ho
  · simpa only [ms_commutator_eq,
      show Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
        (Q c) = U c from rfl] using hfree

include D hf in
/-- Field four supplies a nontrivial scalar and its actual fixed-free cubic
lift on the original whole center. All source and quotient inputs are retained. -/
theorem field_four_center_cubic (hfour : Nat.card F = 4) :
    ∃ k : K c, orderOf (k : G) = 3 ∧
      linearThreeActor e k ∈ center SL(3,F) ∧ linearThreeActor e k ≠ 1 ∧
      U c ⊓ centralizer ({(k : G)} : Set G) = ⊥ := by
  have hz : center SL(3,F) ≠ ⊥ := by
    intro he
    have hh := (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mp he
    exact hh (by rw [hfour])
  obtain ⟨s,hs,hne⟩ := (center SL(3,F)).bot_or_exists_ne_one.resolve_left hz
  obtain ⟨k,hk,ho,hfree⟩ := source_cubic_scalar_lift c D hf 2 (by decide)
    (by simpa using hfour) e s hs hne
  exact ⟨k,ho,hk.symm ▸ hs,(fun he => hne (hk.symm.trans he)),hfree⟩

include D hf e in
/-- At field four the entire original center is moved by the component.
This removes the fixed quotient of U before any natural or upper-section model
is known. -/
theorem field_four_center_moved (hfour : Nat.card F = 4) : ⁅U c,K c⁆ = U c := by
  obtain ⟨k,_,hs,hne,_⟩ := field_four_center_cubic c D hf e hfour
  have hF4 : Nat.card F = 2^2 := by simpa using hfour
  have hpair := msPair_of_quotient c D hf 2 (by decide) hF4 e
  have hfix := (InitialFixed.source_fixed_factors D hf (by decide : 1 < 2) hF4 e).2.1
  have hfix' : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ := by
    simpa only [ms_commutator_eq] using hfix
  simpa only [ms_commutator_eq,
    show Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (Q c) = U c from rfl] using
    InitialDetection.center_moved_eq_self_of_scalar hpair (by decide) hfix' e
      (linearThreeActor e k) hs hne

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.CenterScalars
