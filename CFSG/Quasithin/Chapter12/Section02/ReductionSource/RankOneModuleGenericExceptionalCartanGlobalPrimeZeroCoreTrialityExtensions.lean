module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreTrialityExtensions
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalModuleComparison

/-!
# Triality extension restriction at the original Chapter12 consumer

An escaping Cartan gives a single selected zero-core pair. The actual
triality outer-two-extension normalizers are excluded on that same
pair in both orientations, using the full original hypotheses, Hall data,
residual restriction and universal local control. The selected R retains
its component-or-parabolic source, without an assumed component of H or
an equality sourceS = T.

This discharges one broad original DGS extension row. It does not assert
exhaustive recognition; the remaining cubic rows, independent quintic
result and final hglobal assembly remain with their existing owners.
Source: Aschbacher–Smith 5.2.2, pp.647–648, used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook _root_.Triality.Standard
variable {G : Type*} [Group G] [Finite G]

/-- The original escaping Cartan selects a single prime pair which excludes
all triality outer-two-extension markings, with either orientation. -/
theorem rankOne_cartan_prime_pair_trialityExtensions_of_escape
    {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G)) :
    CartanSmallGeneration A H n ∧
      ∃ (p : ℕ) (D R : Subgroup G), CartanPrimeActor A H p D ∧
        LocalData T L H B D R ∧ SelectedSourceModels H R ∧
        (generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) ∧
        ∀ (m : ℕ) (hm : 0 < m) (E : Subgroup (MulAut (BinaryCarrier m hm)))
          (hE : MulAut.innerSubgroup (BinaryCarrier m hm) ≤ E),
          IsPGroup 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier m hm)))) →
          ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
            (LieModels.Triality.ExtensionAmalgam.amalgam m hm E hE)) ∧
          ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
            (LieModels.Triality.ExtensionAmalgam.amalgam m hm E hE).reverse) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨hs,p,D,R,hd,d,hselected,hzero,hf⟩ :=
    C.rankOne_cartan_smallGeneration_and_prime_pair_of_escape
      h hmany hn hpsl hH hgen hthree c hcontrol hescape
  refine ⟨hs,p,D,R,hd,d,hselected,hzero,hf,?_⟩
  intro m hm E hE h2
  exact d.zeroCore_not_triality_extension_parabolic hi hH c hd hzero m hm E hE h2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
