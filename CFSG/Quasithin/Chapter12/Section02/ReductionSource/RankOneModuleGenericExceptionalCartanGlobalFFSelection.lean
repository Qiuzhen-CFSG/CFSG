module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalFFSelection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicOrbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Selecting the original Cartan FF row and its escaping prime pair

When the Thompson subgroup moves the original L-span of the Sylow
omega-center, the genuine FF classification now selects its natural
fixed quotient or its symmetric-five quotient. The actor and coefficient
maps retain the original two-core and centralizer kernels. The natural
row gives degree two or four and centralization by H; the five row gives
degree two, Cartan centralization of omega and trivial center of H.

Apply small generation to the original CartanLocalControl and escape.
This constructs the same marked prime pair and its zero-core F.1.1 input,
with the original residual and the PSL3(4) exclusion retained. No module
model is assumed in this application. The branch in which Thompson fixes
the omega-span and the subsequent pair recognition remain with assembly.

Source: Aschbacher--Smith 5.1.2, 5.1.6 and 5.2.2, printed pp.630--633,647,
with the 12.2.2 application, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The original escaping Cartan in the Thompson-moving omega branch has
small degree and a literal prime pair, with its module row selected internally. -/
theorem rankOne_cartan_thompson_moving_degree_and_prime_pair_of_escape
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
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) :
    (n = 2 ∨ n = 4) ∧ CartanSmallGeneration A H n ∧
      ((H ≤ omegaCentralizer T ∧
        IsNaturalModule L (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) ∨
       (n = 2 ∧ A ≤ omegaCentralizer T ∧ center H = ⊥)) ∧
      ∃ (p : ℕ) (D R : Subgroup G), CartanPrimeActor A H p D ∧
        LocalData T L H B D R ∧ SelectedSourceModels H R ∧
        (generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  have hz := hcontrol.core_eq_bot_of_not_normalizes le_rfl hescape
  obtain ⟨hdegree,hs,hm⟩ := hi.cartan_thompson_moving_omega_alternatives hH hgen c hz hj
  obtain ⟨p,D,hd⟩ := hs.exists_prime_actor hcontrol hescape
  obtain ⟨R,d,hselected,hzero,hf⟩ := source_prime_pair_zero_core hi hH hgen hthree c hd
  exact ⟨hdegree,hs,hm,p,D,R,hd,d,hselected,hzero,hf⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
