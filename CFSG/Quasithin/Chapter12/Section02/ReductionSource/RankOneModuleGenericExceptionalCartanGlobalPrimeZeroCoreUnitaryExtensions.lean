module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreUnitaryExtensions
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalModuleComparison

/-!
# Unitary extension restrictions at the original chosen-module consumer

The escaping Cartan selects the same zero-core R with its actual component
or diagram-parabolic origin. Every marking in an intermediate subgroup of
the native degree-two unitary extension is excluded on this very pair.
Arbitrary U₅(q) extensions are excluded through their actual base-parabolic
embeddings, in either orientation, using the original quasithin hypothesis.
The original Hall data, universal local control, residual restriction and
sourceS are retained; neither R being a component of H nor sourceS = T is
assumed. The broad DGS classification and its other outer extensions, the
quintic branch and final global normalization remain separate obligations.

Source: Aschbacher–Smith 5.2.2, pp.647–648, used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]

/-- The same escaping source pair excludes all native intermediate unitary
extension markings and arbitrary U₅ extensions, in both orientations. -/
theorem rankOne_cartan_prime_pair_unitaryExtensions_of_escape
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
        (∀ (m : ℕ) (hm : 1 ≤ m) (Y : Subgroup (Extension.ProjectiveExtension m hm)),
          Extension.Intermediate.base m hm ≤ Y →
          ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
            (Extension.Intermediate.amalgam m hm Y)) ∧
          ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
            (Extension.Intermediate.amalgam m hm Y).reverse)) ∧
        ∀ q : ℕ, IsPrimePow q → Even q → ∀ M : UnitaryFive.Model q,
          ¬ ((∃ f : M.leftParabolic →* ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R) : Subgroup G),
                Function.Injective f) ∧
              (∃ f : M.rightParabolic →* (R ⊔ Global.sourceS L H : Subgroup G),
                Function.Injective f)) ∧
          ¬ ((∃ f : M.leftParabolic →* (R ⊔ Global.sourceS L H : Subgroup G),
                Function.Injective f) ∧
              (∃ f : M.rightParabolic →* ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R) : Subgroup G),
                Function.Injective f)) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨hs,p,D,R,hd,d,hselected,hzero,hf⟩ :=
    C.rankOne_cartan_smallGeneration_and_prime_pair_of_escape
      h hmany hn hpsl hH hgen hthree c hcontrol hescape
  refine ⟨hs,p,D,R,hd,d,hselected,hzero,hf,
    fun m hm Y hY => d.zeroCore_not_unitaryIntermediate_parabolic hi hH c hd hzero m hm Y hY,?_⟩
  intro q hq heven M
  constructor
  · rintro ⟨⟨f,hf⟩,⟨g,hg⟩⟩
    exact (d.zeroCore_not_unitaryFive_extension hi hH c hd hzero hq heven M
      (zeroCoreAmalgam L H B D R) f hf g hg).1 ⟨RankTwoAmalgam.ParabolicEquiv.refl _⟩
  · rintro ⟨⟨f,hf⟩,⟨g,hg⟩⟩
    exact (d.zeroCore_not_unitaryFive_extension hi hH c hd hzero hq heven M
      (zeroCoreAmalgam L H B D R).reverse f hf g hg).2 ⟨RankTwoAmalgam.ParabolicEquiv.refl _⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
