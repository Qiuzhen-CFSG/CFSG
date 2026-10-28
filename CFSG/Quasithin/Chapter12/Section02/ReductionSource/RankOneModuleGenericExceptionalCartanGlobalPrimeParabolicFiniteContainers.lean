module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicFiniteContainers
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# Finite common-container reduction on the original Chapter 12 prime pair

The original residual quotient embeds as a section of the literal common
component image. Exact carrier orders and the retained non-PSL₃(4) hypothesis
exclude the alternating, binary higher-linear, small Mathieu and HS rows.
The surviving M₂₄, J₂, J₄, Rudvalis and cubic M₂₂ cases carry the full SL₃(4)
residual and the selected PSL₂(4) parabolic. All original Cartans, Sylow
placements, cubic centers and the strict changed orbit remain explicit.

Source: Aschbacher–Smith 5.2.2, printed pp.648–649, applied in 12.2.2,
printed p.795, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The same chosen pair with the finite common-container exclusions and
actual SL₃(4) marking on the remaining finite rows other than Held. -/
theorem rankOne_cartan_source_parabolic_finite_containers
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
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
            ¬ (R.subgroupOf H).IsCComponent ∧
            (∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
              (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))) ∧
            let X := normalizer (normalizingSylow T R : Set G) ⊔ H
            ∃ I : Subgroup G, residual H ≤ I ∧ I ≤ X ∧
              (I.subgroupOf X).IsCComponent ∧ (I.subgroupOf X).Normal ∧
              conjugateSpanBy R (U : Subgroup G) < I ∧
              let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
              IsQuasisimple Ibar ∧
                ((IsSimpleGroup Ibar ∧
                  (RankTwoTheoremC Ibar ∨ Nonempty (Ibar ≃* Held.He) ∨
                    (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
                      IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 ∧
                      ∃ name : ClassificationModels.SporadicName,
                        (name = .m24 ∨ name = .j2 ∨ name = .j4 ∨ name = .ru) ∧
                        Nonempty (Ibar ≃* name.Carrier)))) ∨
                  (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
                    ((∃ (unitary : Bool) (f : ℕ), 1 ≤ f ∧
                      (2^f) % 3 = (if unitary then 2 else 1) ∧ IsSLSign Ibar unitary 3 (2^f)) ∨
                      (IsM22Cover Ibar ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
                        IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)))))) := by
  exact source_prime_pair_parabolic_finite_containers
    (C.rankOne_generic_input_of_many h hmany hn hpsl) hH hgen hthree c hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
