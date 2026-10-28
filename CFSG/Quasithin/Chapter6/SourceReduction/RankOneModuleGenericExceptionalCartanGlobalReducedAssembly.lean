module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreReducedCatalogue
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalModuleComparison
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicOrbit

/-!
# Cartan normalization from the remaining DGS and quintic sources

The proved source selector constructs one R with its component-or-parabolic
origin, trivial generated core and genuine F.1.1. The quintic source is
applied to that literal pair with [DS:S] = 5. In the cubic case the broad
reduced comparison is transported to the original pair, where all model
and type clauses have been excluded. Small Cartan generation then gives
the required normalization for every universally locally controlled Cartan.

The DGS exhaustive alternatives and quintic opposite-solvability statements
remain explicit earlier-source inputs. This module proves their implication
to SourceCartanPrimeExclusion and hglobal; it does not assert those inputs.
The reduced input is the literal F.1.1 diagram, not an unrelated minimal
DGS pair. Their producers are qt-dgs85-source-assembly and
qt-f112-quintic-solvable-parabolics. The authorized 5.1.13 premise remains
unchanged. Source: Aschbacher–Smith 5.1.6, 5.2.2, pp.631–633,647–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook ChapterF.Source.DGS85.OriginalExtension
open ChapterF.Source.SuzukiContainment
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
          Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup 5)))
    (hquintic : ∀ K R S : Subgroup G, ChapterF.Source.HypothesisF11 ![K,R] S →
      IsQuasithin (ChapterF.Source.generated ![K,R] S) → S ≤ K → S.relIndex K = 5 →
        Group.IsSolvable (ChapterF.Source.parabolic ![K,R] S 1))
include hDGS hquintic

/-- Conditional assembly retaining the broad regular catalogue, unrestricted
U₅ parameter, and literal small type quotients. No final four-row recognition
or source-prime exclusion is assumed. -/
theorem sourceCartanPrimeExclusion_of_reduced_sources :
    SourceCartanPrimeExclusion KnownSimple.IsKnownSimple G := by
  intro _ T L W n h H hH hgen hthree A B c hcontrol hn p D hd
  obtain ⟨R,d,hselected,hz,hf⟩ := source_prime_pair_zero_core h hH hgen hthree c hd
  rcases hd.prime with hp | hp
  · subst p
    rcases hDGS T L W n h H hH hgen hthree A B c hcontrol hn D hd R d hselected hz with
      hc | ⟨q,hq,heven,M,he⟩ | ht
    · exact d.zeroCore_not_reduced_comparison h hH c hd hz hc
    · exact d.zeroCore_not_reduced_unitaryFive h hH c hd hz hq heven M he
    · exact d.zeroCore_not_reduced_small_type h hH c hd hz ht
  · subst p
    exact d.right_parabolic_not_solvable hz
      (hquintic _ _ _ hf (h.qtke.quasithin.subgroup _) le_sup_right
        (Input.prime_left_index h hH c hd))

/-- The exact local-to-global normalization, with only the two independent
remaining source outputs and the authorized earlier 5.1.13 theorem explicit. -/
theorem cartan_normalizes_of_reduced_sources
    (h513 : SourceLocalCartanEscape KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H) :
    A ≤ normalizer (residual H : Set G) :=
  cartan_normalizes_of_prime_sources sourceCartanSmallGeneration
    (sourceCartanPrimeExclusion_of_reduced_sources hDGS hquintic) h513
    h hH hgen hthree c hcontrol

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
