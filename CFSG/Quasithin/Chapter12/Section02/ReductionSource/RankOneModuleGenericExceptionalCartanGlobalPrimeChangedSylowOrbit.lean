module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeChangedSylowOrbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeSourceSieve

/-!
# Changed-orbit obstruction for the original Chapter 12 Cartan pair

The original marked pair supplies the generic input to source 5.2.2.
At an ambient changed Sylow U, the actual orbit ⟨R^U⟩ is not normalized
by T and its residual is not the original O²(H). It is strictly smaller
than the normal orbit of the unique common overcomponent. The proof uses
Hall-preserving Sylow conjugacy and the literal nonzero-core extension.

This retains the smaller containing catalogue and the actual-component
versus parabolic distinction. The source orbit equality needed to exclude
the larger case, compatible zero-core recognition, and higher-field
normalization remain unproved.
Source: Aschbacher–Smith 5.2.2, pp.648–649, applied in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (C : ChosenModule T L V)
include C

/-- Apply the changed-orbit obstruction to the original selected pair,
retaining its actual prime actor, both Hall markings and common component. -/
theorem rankOne_cartan_source_changedSylow_orbit
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
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
          normalizingSylow T R ≤ T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ((T₁ = normalizingSylow T R ∧
            let X := generated L H D R ⊔ normalizingSylow T R
            let q := QuotientGroup.mk' (pCore 2 X)
            ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
              (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
              (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
              RemainingSourceContainer X K) ∨
            (∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
              normalizingSylow T R < T₁ ∧ RemainingLargerSource H R p n ∧
              ¬ (T : Subgroup G) ≤ normalizer (conjugateSpanBy R T₁ : Set G) ∧
              residual (R ⊔ T₁) ≠ residual H ∧
              let X := normalizer (normalizingSylow T R : Set G) ⊔ H
              ∃ I : Subgroup G, R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
                normalizingSylow T R ≤ normalizer (I : Set G) ∧
                (∀ J : Subgroup G, J ≤ X → (J.subgroupOf X).IsCComponent → R ≤ J → J = I) ∧
                let Kplus := conjugateSpanBy I (T : Subgroup G)
                residual H ≤ Kplus ∧ Kplus ≤ X ∧ (Kplus.subgroupOf X).Normal ∧
                  T₁ ≤ normalizer (Kplus : Set G) ∧ conjugateSpanBy R T₁ < Kplus)))) :=
  source_prime_pair_changedSylow_orbit (C.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hgen hthree c hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
