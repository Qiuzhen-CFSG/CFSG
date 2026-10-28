module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldTorus
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicOrbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The original degree-eight Hermitian Cartan branch

Given actual Hermitian coordinates on the original omega-span and H's
centralization of omega, the norm-one torus supplies the order-seventeen
factor with nonzero join core. The remaining order-three and order-five
factors generate the other torus. Universal local control therefore selects
an escaping prime actor in the original Cartan; the established source
construction gives its same marked zero-core pair.

The Hermitian model and omega-centralization remain explicit earlier-source
premises. This does not assert the higher-field selection, degree bound,
zero-core recognition or final local-to-global theorem.
Source: Aschbacher--Smith 5.1.6(4) and 5.2.2, pp.632--633,647,
and the original 12.2.2 application, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open Representation.OrthogonalFourMinus
variable {G : Type*} [Group G] [Finite G]
local instance (s : ℕ) : Algebra (ZMod 2) (FiniteModel.fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (FiniteModel.Space s) :=
  Module.compHom (FiniteModel.Space s) (algebraMap (ZMod 2) (FiniteModel.fixedField s))

/-- The original order-255 Cartan gives an actual prime actor and the literal
zero-core source pair from its Hermitian omega-span, retaining hthree and both
Hall subgroups. The source Sylow is not identified with the ambient T. -/
theorem rankOne_cartan_degree_eight_hermitian_prime_pair
    {T : Sylow 2 G} {L V H A B : Subgroup G}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 8))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G))
    (hHC : H ≤ omegaCentralizer T) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (Representation.SL2.BinarySmall.hermitian s)) :
    CartanSmallGeneration A H 8 ∧
      ∃ (p : ℕ) (D R : Subgroup G), CartanPrimeActor A H p D ∧
        LocalData T L H B D R ∧ SelectedSourceModels H R ∧
        (generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) := by
  let hi := C.rankOne_generic_input_of_many h hmany (by decide : 1 < 8) hpsl
  have hs := hi.cartanSmallGeneration_of_hermitian_degree_eight hH c hHC s hm
  obtain ⟨p,D,hd⟩ := hs.exists_prime_actor hcontrol hescape
  obtain ⟨R,d,hmodel,hzero,hf⟩ := source_prime_pair_zero_core hi hH hgen hthree c hd
  exact ⟨hs,p,D,R,hd,d,hmodel,hzero,hf⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
