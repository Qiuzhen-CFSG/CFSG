module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLargerInvariant
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The moved common container in the original Cartan prime pair

The actual H-component larger-Sylow branch now has a moved common
container of type J₁ or odd-prime PSL₂. The invariant containing branch
is excluded using the original two conjugate components and the literal
Held/Rudvalis involution centralizers. This application retains the same
selected pair, both Cartans, the original non-PSL₃(4) condition, and the
component/parabolic distinction. Source: Aschbacher–Smith 5.2.2, pp.648–649,
applied in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- Retain the original selected pair and its two remaining alternatives.
In the actual-component larger-Sylow branch, the common container is now
necessarily moved; its J₁/odd-prime PSL₂ model and both Sylow intersections
are consequences, not additional source assumptions. -/
theorem rankOne_cartan_source_larger_moved_container
    {T : Sylow 2 G} {L V H A B D : Subgroup G} {n p : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧ RemainingLargerSource H R p n ∧
            ((R.subgroupOf H).IsCComponent →
              let X := normalizer (normalizingSylow T R : Set G) ⊔ H
              ∃ I : Subgroup G, R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
                ¬ (T : Subgroup G) ≤ normalizer (I : Set G) ∧
                (T : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R ∧
                (U : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R ∧
                (U : Subgroup G) ⊓ conjugateSpanBy I (T : Subgroup G) =
                  (T : Subgroup G) ⊓ conjugateSpanBy I (T : Subgroup G) ∧
                (Nonempty ((I ⧸ pCore 2 I) ≃* Janko1.Model) ∨
                  ∃ q : ℕ, q.Prime ∧ Odd q ∧ ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 q)))) := by
  exact source_prime_pair_larger_moved_container
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH hgen hthree c hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
