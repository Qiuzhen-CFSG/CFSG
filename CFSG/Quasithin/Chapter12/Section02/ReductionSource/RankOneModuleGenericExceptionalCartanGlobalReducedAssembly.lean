module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalReducedAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalModuleComparison

/-!
# The remaining DGS inputs at the Chapter 12 Cartan consumer

The whole chosen reduced module supplies the original Input. The completed
small-generation and source-prime-pair construction, together with the
literal reduced-diagram restriction, discharge the hglobal callback of the
existing exceptional assembly. The displayed DGS and quintic source outputs
still require their independent proofs; 5.1.13 retains its existing producer.
The universal local control, original residual, Hall Cartans and hthree are
unchanged. Source: Aschbacher–Smith 5.2.2 and 12.2.2, pp.647–649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook ChapterF.Source.DGS85.OriginalExtension
open ChapterF.Source.SuzukiContainment
universe u
variable {G : Type u} [Group G] [Finite G]
/-- An escaping original Cartan produces one pair whose complete reduced
marking is the original diagram and whose compatible restored completions
have no outer enlargement. The same R and original Hall overlap are used
in both conclusions. -/
theorem rankOne_cartan_reduced_extension_of_escape
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
    ∃ (p : ℕ) (D R : Subgroup G) (hd : CartanPrimeActor A H p D)
      (d : LocalData T L H B D R) (hz : (generated L H D R).pCoreIn 2 = ⊥),
      SelectedSourceModels H R ∧
      Nonempty (Iso (zeroCoreAmalgam L H B D R)
        (reducedAmalgam ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H))) ∧
      ∀ (X : Type u) [Group X]
        (f : FaithfulCompletion
          (reducedAmalgam ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) (G := X))
        (hk : PreservesCompletionKernel (d.hypothesisF11
          (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz) f),
        f.left.range ⊓ f.right.range = f.middle.range →
        (∀ i, normalizer ((completionEndpoint f i).range : Set X) =
          (completionEndpoint f i).range) →
        automorphismExtension (d.hypothesisF11
          (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz) f hk =
          MulAut.innerSubgroup X := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨hs,p,D,R,hd,d,hselected,hz,_⟩ :=
    C.rankOne_cartan_smallGeneration_and_prime_pair_of_escape
      h hmany hn hpsl hH hgen hthree c hcontrol hescape
  refine ⟨hs,p,D,R,hd,d,hz,hselected,⟨d.zeroCoreReducedIso hi hH c hd hz⟩,?_⟩
  intro X _ f hk ho hN
  exact d.zeroCore_automorphismExtension_eq_inner hi hH c hd hz f hk ho hN

variable
    (hDGS : ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ),
      Input KnownSimple.IsKnownSimple T L W n →
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        1 < ChapterE.generationParameter H →
        ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
        ∀ A B : Subgroup G, CartanPair T L H A B → CartanLocalControl A H →
        (n = 2 ∨ n = 4 ∨ n = 8) →
        ∀ D : Subgroup G, CartanPrimeActor A H 3 D →
        ∀ R : Subgroup G, LocalData T L H B D R → SelectedSourceModels H R →
        (generated L H D R).pCoreIn 2 = ⊥ →
        let α := reducedAmalgam ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)
        let P := ChapterF.Source.parabolic ![D ⊔ Global.sourceS L H,R]
          (reducedSylow ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) 1
        Global.ConcreteAmalgamComparison α ∨
        (∃ (q : ℕ) (_ : IsPrimePow q) (_ : Even q) (M : UnitaryFive.Model q),
          Nonempty (Iso α M.amalgam) ∨ Nonempty (Iso α M.amalgam.reverse)) ∨
        (ClassicalGroup.IsPSL (P ⧸ pCore 2 P) 2 2 ∨
          Nonempty ((P ⧸ pCore 2 P) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
          Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup 5)))
    (hquintic : ∀ K R S : Subgroup G, ChapterF.Source.HypothesisF11 ![K,R] S →
      IsQuasithin (ChapterF.Source.generated ![K,R] S) → S ≤ K → S.relIndex K = 5 →
        Group.IsSolvable (ChapterF.Source.parabolic ![K,R] S 1))
include hDGS hquintic

/-- The literal Chapter 12 hglobal application on the original Cartan. -/
theorem rankOne_cartan_normalizes_of_reduced_sources
    {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (h513 : SourceLocalCartanEscape KnownSimple.IsKnownSimple G) :
    A ≤ normalizer (residual H : Set G) :=
  cartan_normalizes_of_reduced_sources hDGS hquintic h513
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH hgen hthree c hcontrol

/-- Apply the proved local-to-global implication to the existing exceptional
assembly. Neither small generation, prime-pair construction nor hglobal is
an additional callback; the two earlier source outputs remain explicit. -/
theorem rankOne_exceptional_cartan_of_reduced_sources
    {T : Sylow 2 G} {L V H : Subgroup G}
    (C : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hescape : ¬ (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G))
    (hprepare : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) n →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      1 < ChapterE.generationParameter H → CartanPreparation T L H)
    (hlocal : SourceLocalCartanEscape KnownSimple.IsKnownSimple G) :
    CartanExceptionalConclusion T L (RankOneModule.wholeReduced T L) H ∧
      RankOneModule.ExceptionalExit T L H ∧ n = 2 ∧
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module := by
  apply C.rankOne_exceptional_cartan_of_source h hmany hn hpsl hH hgen hthree
    hescape hprepare hlocal
  intro h513 hi hHs hgs hts A B c hcontrol
  exact cartan_normalizes_of_reduced_sources hDGS hquintic h513 hi hHs hgs hts c hcontrol

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
