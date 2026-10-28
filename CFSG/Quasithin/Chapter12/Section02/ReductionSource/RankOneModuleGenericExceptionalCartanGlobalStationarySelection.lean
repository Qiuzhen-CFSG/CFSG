module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalStationarySelection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicOrbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The actual escaping prime pair in the stationary Thompson branch

Apply the complete stationary constituent argument to the literal whole
reduced module from Chapter12. Both natural and Hermitian rows now give
small Cartan generation, using their original central Sylow seeds. This
constructs the same escaping prime pair, SelectedSourceModels and F.1.1,
without any supplied model, constituent invariance or degree bound.

The original Hall Cartans, universal local control, H-star membership,
generation bound, residual and PSL₃(4) exclusion are preserved. The later
zero-core completion and changed-Sylow recognition remain with assembly.

Source: Aschbacher--Smith 5.1.3, 5.1.6 and 5.2.2, pp.630--633,647,
with the 12.2.2 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The stationary original Thompson action supplies small generation and
the literal escaping prime pair, with every constituent model selected internally. -/
theorem rankOne_cartan_stationary_degree_and_prime_pair_of_escape
    {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G))
    (hj : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (RankOneModule.wholeReduced T L : Set G)) :
    H ≤ omegaCentralizer T ∧ CartanSmallGeneration A H n ∧
      ∃ (p : ℕ) (D R : Subgroup G), CartanPrimeActor A H p D ∧
        LocalData T L H B D R ∧ SelectedSourceModels H R ∧
        (generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨hHC,hs⟩ := hi.cartanSmallGeneration_of_thompson_centralizes hH c hcontrol hescape hj
  obtain ⟨p,D,hd⟩ := hs.exists_prime_actor hcontrol hescape
  obtain ⟨R,d,hselected,hzero,hf⟩ := source_prime_pair_zero_core hi hH hgen hthree c hd
  exact ⟨hHC,hs,p,D,R,hd,d,hselected,hzero,hf⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
