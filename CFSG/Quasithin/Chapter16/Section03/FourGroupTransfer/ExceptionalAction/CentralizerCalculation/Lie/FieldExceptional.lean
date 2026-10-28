module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.Basic
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Quotient
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldExceptional.Transport
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Exceptional field-pair fixer bounds: transport and model obligations

The actual quotient map sends L to a component of the distinguished
involution's fixed subgroup in the specified model. Its central quotient
is L/O₂(L). Thus model calculations for such embedded components transfer
to the pair fixer upstairs by faithful automorphism descent.

The two intrinsic fixer calculations remain explicit inputs below. They
require the actual component embedding; an abstract fixed-group equivalence
does not supply them. Both larger models inherit simplicity and perfectness
from the source component, so their separate certification is not required.
The smaller model remains a derived subgroup, including G₂(2)′, and triality
uses the genuine Standard.BinaryCarrier construction throughout.

Source: Aschbacher–Smith, 16.1.4(4), 16.1.7(3a), and 16.3.5, printed
pp.1171–1173 and 1178–1179 of the 1 March 2004 manuscript.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldExceptional
open Subgroup Theory.GroupTheory
open CounterexampleGeometry.CoveredPersistence

/-- The outstanding intrinsic calculation in the actual split G₂ model.
The smaller central quotient is derived even at field order two. -/
def G2ComponentFixerBound : Prop :=
  ∀ (F k : Type) [Field F] [Field k] [Finite F] [Finite k]
    [IsSimpleGroup (Atlas.G2.Model F)] [Group.IsPerfect (Atlas.G2.Model F)]
    (n : ℕ), 1 ≤ n → Nat.card F = 2 ^ (2 * n) → Nat.card k = 2 ^ n →
    ∀ (a : MulAut (Atlas.G2.Model F)), orderOf a = 2 →
    ∀ (J : Subgroup (Atlas.G2.Model F)), IsComponentIn J a.fixedSubgroup →
    Nonempty ((J ⧸ center J) ≃* commutator (Atlas.G2.Model k)) →
      Nat.card (fixingSubgroup (MulAut (Atlas.G2.Model F)) (J : Set (Atlas.G2.Model F))) ≤ 2

/-- The independent intrinsic calculation on genuine triality carriers.
No simplicity assumption is added for the smaller carrier. -/
def TrialityComponentFixerBound : Prop :=
  ∀ (n : ℕ) (hn : 0 < n),
    let S := Triality.Standard.BinaryCarrier (2 * n) (by omega)
    ∀ [IsSimpleGroup S] [Group.IsPerfect S]
      (a : MulAut S), orderOf a = 2 →
      ∀ (J : Subgroup S), IsComponentIn J a.fixedSubgroup →
      Nonempty ((J ⧸ center J) ≃* commutator (Triality.Standard.BinaryCarrier n hn)) →
        Nat.card (fixingSubgroup (MulAut S) (J : Set S)) ≤ 2

private def commutatorEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    commutator A ≃* commutator B :=
  (e.subgroupMap (commutator A)).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
    rfl))

universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {E L I : Subgroup G} {t i : G}

/-- Conditional specialization of the intrinsic G₂ calculation to the actual
central-cover pair. The intrinsic input must be proved for final assembly. -/
theorem pairFixer_card_lt_four_g2_of_model_bound (bound : G2ComponentFixerBound)
    (hG : Hypothesis1611 𝒦 G) (h : PairContext E L I t i)
    (n : ℕ) (hn : 1 ≤ n)
    (hlarge : FieldFamily.g2.ModelAt (I ⧸ pCore 2 I) (2 ^ (2 * n)))
    (hsmall : FieldFamily.g2.DerivedAt (L ⧸ pCore 2 L) (2 ^ n)) :
    Nat.card (pairFixer L I) < 4 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hlarge
  obtain ⟨M, _, _, hM, ⟨em⟩⟩ := hsmall
  obtain ⟨k, _, _, hk, ⟨ek⟩⟩ := hM
  let := model_isSimpleGroup h hG e
  let := model_isPerfect h hG e
  have hj : Nonempty ((modelComponent h hG e ⧸ center (modelComponent h hG e)) ≃*
      commutator (Atlas.G2.Model k)) :=
    ⟨(componentCentralQuotientEquiv h hG e).trans (em.trans (commutatorEquiv ek))⟩
  have hb := bound F k n hn hF hk (modelInvolution h hG e)
    (modelInvolution_orderOf h hG e) (modelComponent h hG e)
    (modelComponent_isComponentIn h hG e) hj
  exact pairFixer_card_lt_of_cover (h.coreCover hG e) (h.coreCover_kernel hG e)
    (hb.trans_lt (by decide))

/-- Conditional specialization to the actual standard triality models,
including the genuine derived endpoint at n = 1. -/
theorem pairFixer_card_lt_four_triality_of_model_bound
    (bound : TrialityComponentFixerBound)
    (hG : Hypothesis1611 𝒦 G) (h : PairContext E L I t i)
    (n : ℕ) (hn : 1 ≤ n)
    (hlarge : FieldFamily.triality.ModelAt (I ⧸ pCore 2 I) (2 ^ (2 * n)))
    (hsmall : FieldFamily.triality.DerivedAt (L ⧸ pCore 2 L) (2 ^ n)) :
    Nat.card (pairFixer L I) < 4 := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff
    (I ⧸ pCore 2 I) (2 * n) (by omega)).mp hlarge
  obtain ⟨M, _, _, hM, ⟨em⟩⟩ := hsmall
  obtain ⟨ek⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff M n (by omega)).mp hM
  let := model_isSimpleGroup h hG e
  let := model_isPerfect h hG e
  have hj : Nonempty ((modelComponent h hG e ⧸ center (modelComponent h hG e)) ≃*
      commutator (Triality.Standard.BinaryCarrier n (by omega))) :=
    ⟨(componentCentralQuotientEquiv h hG e).trans (em.trans (commutatorEquiv ek))⟩
  have hb := bound n (by omega) (modelInvolution h hG e)
    (modelInvolution_orderOf h hG e) (modelComponent h hG e)
    (modelComponent_isComponentIn h hG e) hj
  exact pairFixer_card_lt_of_cover (h.coreCover hG e) (h.coreCover_kernel hG e)
    (hb.trans_lt (by decide))

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldExceptional
