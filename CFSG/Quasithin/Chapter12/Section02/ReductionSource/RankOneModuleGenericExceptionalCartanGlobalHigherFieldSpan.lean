module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldSpan
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The original escaping Hermitian Cartan and its reduced torus module

Apply the fixed-line and reduced-closure calculation to the same plus
torus selected by universal local control. Its join with H retains zero
two-core, while its original omega-span has order 2^(n/2), equals the
whole Cartan span and is reduced in the actual plus-torus/Sylow join.
The original Cartans, residual, quotient action and Sylow are retained.
Model selection, the numerical degree bound and zero-core recognition
remain with the source normalization argument.

Source: Aschbacher--Smith 5.1.6(4), 5.2.2 and 12.2.2, printed
pp.632--633,647,795 (`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open Representation.OrthogonalFourMinus.FiniteModel
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
local instance (s : ℕ) : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The original escaping Hermitian Cartan supplies its actual reduced
plus-torus module, with its full fixed-line identification and original degree. -/
theorem rankOne_cartan_hermitian_reduced_torus_of_escape
    {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 2 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G)) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s)) :
    4 ∣ n ∧ ∃ Dminus Dplus : Subgroup G,
      Dminus ⊔ Dplus = A ∧ Nat.card Dminus = 2^(n/2)+1 ∧
      Nat.card Dplus = 2^(n/2)-1 ∧
      Dminus ⊔ H ≤ omegaCentralizer T ∧
      (Dminus ⊔ H).pCoreIn 2 ≠ ⊥ ∧
      Dminus ≤ normalizer (residual H : Set G) ∧
      (Dplus ⊔ H).pCoreIn 2 = ⊥ ∧
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let U := conjugateSpanBy Z L
      let X := conjugateSpanBy Z Dplus
      X = conjugateSpanBy Z A ∧
      X = U ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
      Nat.card X = 2^(n/2) ∧
      A ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
      Dplus ⊓ centralizer (X : Set G) = ⊥ ∧
      X ∈ reducedFamily (Dplus ⊔ (T : Subgroup G)) := by
  let hi := C.rankOne_generic_input_of_many h hmany (by omega : 1 < n) hpsl
  obtain ⟨hfour,Dm,Dp,hjoin,hmc,hpc,hcentral,hcore,hmN,hzero⟩ :=
    hi.hermitian_torus_of_escape hH c hn hcontrol hescape s hm
  have he := hi.exponent_of_hermitian_model s hm
  have hh : n/2=s := by omega
  have hDA : Dp ≤ A := hjoin ▸ le_sup_right
  have hDc : Nat.card Dp = 2^s-1 := by simpa only [hh] using hpc
  obtain ⟨hline,hcard,hnorm,hfaith⟩ := hi.hermitian_plus_span c s hm hDA hDc
  obtain ⟨hspan,hred⟩ := hi.hermitian_plus_span_reduced c s hm hDA hDc
  exact ⟨hfour,Dm,Dp,hjoin,hmc,hpc,hcentral,hcore,hmN,hzero,
    hspan,hline,by simpa only [hh] using hcard,hnorm,hfaith,hred⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
