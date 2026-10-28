module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalExtensionAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalModuleComparison

/-!
# Original Lie extensions at the Chapter 12 Cartan consumer

The whole chosen reduced module supplies the original Input. The extended
source sieve now allows full symplectic, G₂ and Ree extensions in either
orientation, with their actual whole overlap. Its endpoint-solvability
restriction discharges those rows before the existing prime-exclusion and
small-generation argument is applied to hglobal.

DGS exhaustiveness and the exact quintic source result remain independent
inputs. Universal local control, the original residual and Hall Cartans,
hthree, the full known-simple catalogue and the authorized 5.1.13 premise
are retained. Source: Aschbacher–Smith 5.2.2 and 12.2.2, pp.647–649,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook ChapterF.Source.DGS85.OriginalExtension
open ChapterF.Source.SuzukiContainment
open ChapterF.SourceCompletion.UnitaryNonbinary
universe u
variable {G : Type u} [Group G] [Finite G]
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
          Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup 5)) ∨
        (∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
            (m : ℕ) (_ : 0 < m) (_ : Nat.card F = 2^m)
            (E : SourceExtension
              (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F))
              (Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F))),
          Nonempty (Iso (zeroCoreAmalgam L H B D R) E.amalgam) ∨
          Nonempty (Iso (zeroCoreAmalgam L H B D R) E.amalgam.reverse)) ∨
        (∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
            (m : ℕ) (_ : 0 < m) (_ : Nat.card F = 2^m)
            (E : SourceExtension (Atlas.G2.LieParabolicSetup.parabolic₁ (F := F))
              (Atlas.G2.LieParabolicSetup.parabolic₂ (F := F))),
          Nonempty (Iso (zeroCoreAmalgam L H B D R) E.amalgam) ∨
          Nonempty (Iso (zeroCoreAmalgam L H B D R) E.amalgam.reverse)) ∨
        (∃ (m : ℕ) (E : SourceExtension (ReeF4.Parabolics.parabolic m .suzuki)
            (ReeF4.Parabolics.parabolic m .linear)),
          Nonempty (Iso (zeroCoreAmalgam L H B D R) E.amalgam) ∨
          Nonempty (Iso (zeroCoreAmalgam L H B D R) E.amalgam.reverse)))
    (hquintic : ∀ K R S : Subgroup G, ChapterF.Source.HypothesisF11 ![K,R] S →
      IsQuasithin (ChapterF.Source.generated ![K,R] S) → S ≤ K → S.relIndex K = 5 →
        Group.IsSolvable (ChapterF.Source.parabolic ![K,R] S 1))
include hDGS hquintic

/-- The literal Chapter 12 hglobal application on the original Cartan. -/
theorem rankOne_cartan_normalizes_of_extension_sources
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
  cartan_normalizes_of_extension_sources hDGS hquintic h513
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH hgen hthree c hcontrol

/-- Apply the proved local-to-global implication to the existing exceptional
assembly. Neither small generation, prime-pair construction nor hglobal is
an additional callback; the two earlier source outputs remain explicit. -/
theorem rankOne_exceptional_cartan_of_extension_sources
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
  exact cartan_normalizes_of_extension_sources hDGS hquintic h513 hi hHs hgs hts c hcontrol

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
