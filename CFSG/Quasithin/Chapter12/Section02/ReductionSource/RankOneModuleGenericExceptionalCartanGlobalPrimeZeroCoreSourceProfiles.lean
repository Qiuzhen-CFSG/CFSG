module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreSourceProfiles
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreTrialityExtensions

/-!
# Earlier DGS profiles on the same original Chapter 12 pair

The escaping Cartan selects one zero-core pair. Its full Borel core is
exactly the original sourceS; the Chapter 11 binary elementary seed count
on that core contradicts the strict source size bound. Solvable type
clauses on the actual reduced generated starred right quotient are also
excluded by inclusion-induced quotient transport. The triality extension
restrictions are retained for this very same selected R.

The original hthree, universal local control, Hall data and selected-model
witnesses remain unchanged. Earlier DGS classification and seed geometry,
quintic solvability and final hglobal discharge remain source obligations.
Source: Aschbacher–Smith 5.2.2, pp.647–648, used in 12.2.2, p.795;
DGS85 (11.7), (13.1) and (15.1), pp.174,191,226.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook _root_.Triality.Standard
open ChapterF.Source.DGS85.CommutingOneProfile ChapterF.Source.DGS85.CommutingThreeProfile
variable {G : Type*} [Group G] [Finite G]

/-- The literal selected pair rejects the earlier elementary and solvable
quotient profiles, while retaining its original triality extension exclusions. -/
theorem rankOne_cartan_prime_pair_sourceProfiles_of_escape
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
        (Global.sourceS L H ⊔ (B ⊓ R)).pCoreIn 2 = Global.sourceS L H ∧
        (∀ (X : Type) [Group X] [Group.IsSolvable X],
          ¬ Nonempty ((reducedGeneratedStarred ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 1 ⧸
            pCore 2 (reducedGeneratedStarred ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 1)) ≃* X)) ∧
        (∀ (Z Z' : Subgroup G) (g : G),
          g ∈ (D ⊔ Global.sourceS L H) ⊔ (B ⊓ R) →
          Z.map (MulAut.conj g).toMonoidHom = Z' →
          ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2 ≤ normalizer (Z : Set G) →
          ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2 =
            pairSpan Z Z' (((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2) →
          (Global.sourceS L H ⊔ (B ⊓ R)).pCoreIn 2 =
            Z ⊔ ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2 →
          Nat.card Z = 16 →
          (Z ⊓ ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2).relIndex Z = 2 →
          Nat.card ((Z ⊓ ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2) ⊓
            (Z' ⊓ ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)).pCoreIn 2) : Subgroup G) = 2 → False) ∧
        ∀ (m : ℕ) (hm : 0 < m) (E : Subgroup (MulAut (BinaryCarrier m hm)))
          (hE : MulAut.innerSubgroup (BinaryCarrier m hm) ≤ E),
          IsPGroup 2 (E.map (QuotientGroup.mk' (MulAut.innerSubgroup (BinaryCarrier m hm)))) →
          ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
            (LieModels.Triality.ExtensionAmalgam.amalgam m hm E hE)) ∧
          ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
            (LieModels.Triality.ExtensionAmalgam.amalgam m hm E hE).reverse) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨hs,p,D,R,hd,d,hselected,hzero,hf,htriality⟩ :=
    C.rankOne_cartan_prime_pair_trialityExtensions_of_escape
      h hmany hn hpsl hH hgen hthree c hcontrol hescape
  refine ⟨hs,p,D,R,hd,d,hselected,hzero,hf,
    d.zeroCore_borel_core_eq_sourceS hi hH c hd hzero,?_,?_,htriality⟩
  · intro X _ _ he
    exact d.zeroCore_no_solvable_reduced_right_quotient hi hH c hd hzero he.some
  · intro Z Z' g hg hconj hn hcore hB hZ hindex hinter
    exact d.zeroCore_no_elementary_binary_profile hi hH c hd hzero
      Z Z' g hg hconj hn hcore hB hZ hindex hinter

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
