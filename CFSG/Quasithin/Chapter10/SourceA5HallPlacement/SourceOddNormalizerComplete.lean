module

public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.SourceUnitaryFourQuotients

/-!
# Complete odd-normalizer control for the original nonnormal A₅ setup

The intrinsic Sylow quotient condition is now proved for both remaining
unitary families. It discharges the last model premise in the original
odd-normalizer argument. Applying that result to the actual Hall-kernel
actor makes the original full-Hall witness faithful and gives the original
separated-module generation bound.

The Hall and generation conclusions retain their literal original
coordinate or separation hypotheses. No unitary, quotient-action, component
placement, or odd-normalizer premise remains.

Source: Aschbacher--Smith 4.4.3, 4.4.10--14, and 10.2.1.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original suitable odd actor has its full normalizer inside the
chosen maximal local subgroup, with every model condition discharged. -/
theorem source_a5_oddPrimeNormalizer_control
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    normalizer (B : Set G) ≤ D.maximalLocal :=
  source_a5_oddPrimeNormalizer_control_of_unitary_sylow_quotients
    D e hn source_oddUnitarySylowQuotients hp B hne hB hBC hBV hperm

/-- The original full-Hall witness is faithful on the actual local orbit;
its Hall subgroup, ambient image and coordinate hypotheses are unchanged. -/
theorem source_a5_hstar_hall_faithful
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcoords : SourceA5OriginalBoundedSeparatedCoordinates D e hn ht htn)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    ∃ B : Subgroup H, B ≤ D.maximalLocal.subgroupOf H ∧
      IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)) ∧
      B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ :=
  source_a5_hstar_hall_faithful_of_unitary_sylow_quotients
    D e hn source_oddUnitarySylowQuotients ht htn hcoords hH hlarge

/-- The original separated minimal setup has generation parameter at most
two, with its source odd-normalizer and full-Hall obligations discharged. -/
theorem source_a5_hstar_generation_bound
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    generationParameter H ≤ 2 :=
  source_a5_hstar_generation_bound_of_unitary_sylow_quotients
    D e hn source_oddUnitarySylowQuotients ht htn hD hbound hsep hH

end CFSG.Quasithin.Chapter10
