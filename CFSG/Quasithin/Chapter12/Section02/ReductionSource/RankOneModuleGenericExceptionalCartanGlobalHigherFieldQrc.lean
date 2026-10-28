module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldQrc
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalHigherFieldSpan

/-!
# The original escaping Cartan supplies the qrc numerical bound

Apply the common-normal qrc argument to the same plus torus supplied by
universal local control. Its literal omega-span retains order 2^(n/2)
and the full Cartan span. The original H, Sylow subgroup, residual and
Hall markings are unchanged. Both the genuine qrc configuration and the
cubic-ratio upper bound are constructed, without a uniqueness premise
for the smaller torus join. Model selection and the semilinear degree
bound remain with the original normalization argument.

Source: Aschbacher--Smith 5.1.6(4), 5.2.2 and 12.2.2,
printed pp.632--633,647,795 (`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.OrthogonalFourMinus.FiniteModel
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
local instance (s : ℕ) : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The same original escaping Hermitian Cartan supplies a genuine qrc
pair and the cubic bound on its literal plus-torus conjugation action. -/
theorem rankOne_cartan_hermitian_qrc_bound_of_escape
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
      Dminus ≤ normalizer (residual H : Set G) ∧
      (Dplus ⊔ H).pCoreIn 2 = ⊥ ∧
      let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Dplus
      X = conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A ∧
      Nat.card X = 2^(n/2) ∧
      ChapterD.QRCConfiguration (Dplus ⊔ (T : Subgroup G)) H (T : Subgroup G) X ∧
      ∃ hq : Chapter3.QrcHypotheses T (normalizer (L : Set G))
          (Dplus ⊔ (T : Subgroup G)) H X,
        letI := hq.module_elementary
        cubicRatio (ChapterD.UniqueFactor.imageRepresentation
          (Dplus ⊔ (T : Subgroup G)) X hq.module_normalized) ≤ 2 := by
  let hi := C.rankOne_generic_input_of_many h hmany (by omega : 1 < n) hpsl
  obtain ⟨hfour,Dm,Dp,hjoin,hmc,hpc,hcentral,hcore,hmN,hzero⟩ :=
    hi.hermitian_torus_of_escape hH c hn hcontrol hescape s hm
  have he := hi.exponent_of_hermitian_model s hm
  have hh : n/2=s := by omega
  have hs : 1 < s := by omega
  have hDA : Dp ≤ A := hjoin ▸ le_sup_right
  have hDc : Nat.card Dp = 2^s-1 := by simpa only [hh] using hpc
  obtain ⟨hspan,hred⟩ := hi.hermitian_plus_span_reduced c s hm hDA hDc
  have hcard := (hi.hermitian_plus_span c s hm hDA hDc).2.1
  exact ⟨hfour,Dm,Dp,hjoin,hmc,hpc,hmN,hzero,hspan,by simpa only [hh] using hcard,
    hi.hermitian_plus_qrc_configuration hH c s hs hm hDA hDc hzero,
    hi.hermitian_plus_qrc_hypotheses hH c s hs hm hDA hDc,
    hi.hermitian_plus_cubicRatio_le_two hH c s hs hm hDA hDc hzero⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
