module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeCommonSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The common-component Sylow intersections in original 12.2.2

Apply the source common-orbit comparison to the literal changed Sylow of
the original marked Cartan pair. The larger-Sylow branch retains the same
unique containing component I, its normal orbit Kplus, and the strict
containment of the selected R-orbit. If I is moved, both Sylow normalizers
of I are T₀ and their intersections with Kplus agree. The source model
comparison then forces the original R to be an actual A₅ H-component,
with p = 5, n ≠ 2, and containing quotient J₁ or odd-prime PSL₂.

This supplies the moved-common-component intersection step in 5.2.2.
It does not identify R with I or prove the remaining original-residual
comparison. Source: Aschbacher–Smith 5.2.2, pp.648–649, used in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D R : Subgroup G} (C : ChosenModule T L V)
include C

/-- The actual chosen-module pair has a common orbit for both ambient
Sylows, with exact intersection and normalizer comparisons when I moves. -/
theorem rankOne_prime_changedSylow_common_orbit
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
    ∃ P : Sylow 2 (extension T L H B D R),
      let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
      normalizingSylow T R ≤ T₁ ∧
      (T₁ = normalizingSylow T R ∨ ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
        let X := normalizer (normalizingSylow T R : Set G) ⊔ H
        ∃ I : Subgroup G, R < I ∧ I ≤ X ∧ (I.subgroupOf X).IsCComponent ∧
          normalizingSylow T R ≤ normalizer (I : Set G) ∧
          (∀ J : Subgroup G, J ≤ X → (J.subgroupOf X).IsCComponent → R ≤ J → J = I) ∧
          let Kplus := conjugateSpanBy I (T : Subgroup G)
          residual H ≤ Kplus ∧ Kplus ≤ X ∧ (Kplus.subgroupOf X).Normal ∧
            T₁ ≤ normalizer (Kplus : Set G) ∧ conjugateSpanBy R T₁ < Kplus ∧
            conjugateSpanBy I T₁ = Kplus ∧ Kplus ≤ normalizer (I : Set G) ∧
            (¬ (T : Subgroup G) ≤ normalizer (I : Set G) →
              (T : Subgroup G) ⊓ normalizer (I : Set G) = normalizingSylow T R ∧
              (T : Subgroup G) ⊓ Kplus = normalizingSylow T R ⊓ Kplus ∧
              T₁ ⊓ Kplus = (T : Subgroup G) ⊓ Kplus ∧
              ¬ T₁ ≤ normalizer (I : Set G) ∧
              T₁ ⊓ normalizer (I : Set G) = normalizingSylow T R)) := by
  obtain ⟨P,hTP,_,hcases⟩ := d.exists_changedSylow hH.1.1.2 c hd hz
  refine ⟨P,hTP,?_⟩
  rcases hcases with he | ⟨U,hU⟩
  · exact .inl he
  · exact .inr ⟨U,hU,d.changedSylow_common_orbit_geometry
      (C.rankOne_generic_input_of_many h hmany hn hpsl) hH c hd hz P hTP hU⟩

/-- Movement of the selected common overcomponent puts the actual original
right factor in the exceptional A₅ branch, with only J₁ or prime PSL₂ above it. -/
theorem rankOne_prime_moved_common_component_models
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (d : LocalData T L H B D R)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hs : SelectedSourceModels H R) {I : Subgroup G} (hRI : R < I)
    (hIX : I ≤ normalizer (normalizingSylow T R : Set G) ⊔ H)
    (hI : (I.subgroupOf (normalizer (normalizingSylow T R : Set G) ⊔ H)).IsCComponent)
    (hu : ∀ J : Subgroup G, J ≤ normalizer (normalizingSylow T R : Set G) ⊔ H →
      (J.subgroupOf (normalizer (normalizingSylow T R : Set G) ⊔ H)).IsCComponent →
      R ≤ J → J = I)
    (hm : ¬ (T : Subgroup G) ≤ normalizer (I : Set G)) :
    (R.subgroupOf H).IsCComponent ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 ∧
      p = 5 ∧ n ≠ 2 ∧
      (Nonempty ((I ⧸ pCore 2 I) ≃* Janko1.Model) ∨
        ∃ q : ℕ, q.Prime ∧ Odd q ∧ ClassicalGroup.IsPSL (I ⧸ pCore 2 I) 2 q) :=
  d.moved_common_component_models (C.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hgen hthree c hd hz hs hRI hIX hI hu hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
