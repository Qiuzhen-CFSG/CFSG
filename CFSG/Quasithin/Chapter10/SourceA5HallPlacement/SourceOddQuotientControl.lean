module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.SourceOddSolvableLift
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentInspection
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.FullEscape
public import Theory.GroupTheory.SolvableQuotientPair

/-!
# The original odd-normalizer and Hall consumers from two Sylow quotients

All previously completed model exclusions leave only PSU4(2^f), f at
least three, and PSU5(4). An escaping original actor therefore selects a
normal component in one of these families for which no Sylow automorphism
group has two quotient actions of the indicated orders with solvable common
kernel. This is an unconditional obstruction on the actual component.

The converse consumer takes precisely the still-unproved intrinsic quotient
condition for those two families. Solvable lifting proves inner action,
covering uniqueness proves placement, and the completed local inspection
excludes the component. The resulting original normalizer control feeds
the literal full-Hall witness and generation bound. The intrinsic unitary
condition remains explicit; no unitary automorphism classification is asserted.

Source: Aschbacher--Smith 4.4.3, 4.4.10--14, and 10.2.1.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
universe u

/-- The precise outstanding intrinsic model condition. Two quotient actions
suffice; full outer solvability and exclusion of all product sections are
not assumed. This definition does not assert the condition. -/
@[expose] def SourceOddUnitarySylowQuotients : Prop :=
  ∀ (S : Type u) [Group S] [Finite S], IsSimpleGroup S →
    ((∃ f : ℕ, 3 ≤ f ∧ ClassicalGroup.IsPSU S 4 (2 ^ f)) ∨
      ClassicalGroup.IsPSU S 5 4) →
    ∃ P : Sylow 2 S, HasSolvableQuotientPair 25 (MulAut P)

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Every escaping original actor selects an actual normal binary-unitary
component without the indicated two quotient actions on any Sylow group. -/
theorem source_a5_oddPrimeNormalizer_unitary_without_sylow_quotients
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (hout : ¬ normalizer (B : Set G) ≤ D.maximalLocal) :
    ∃ K : Subgroup (normalizer (B : Set G)),
      IsComponent (normalizer (B : Set G)) K ∧ K.Normal ∧
      ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal ∧
      ((∃ f : ℕ, 3 ≤ f ∧ ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ f)) ∨
        ClassicalGroup.IsPSU (K ⧸ center K) 5 4) ∧
      ∀ P : Sylow 2 (K ⧸ center K), ¬ HasSolvableQuotientPair 25 (MulAut P) := by
  obtain ⟨K,hK,hKN,houtK,hFK,hm⟩ :=
    source_a5_oddPrimeNormalizer_remaining_unitary_component
      D e hn hp B hne hB hBC hBV hperm hout
  refine ⟨K,hK,hKN,houtK,hm,?_⟩
  intro P ⟨A,C,hAN,hCN,hAC,hA,hC⟩
  let := hKN
  let := hAN
  let := hCN
  let : IsQuasisimple K := hK.2
  exact source_a5_oddNormalizer_no_inner_component
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
      (source_a5_oddNormalizer_inner_of_sylow_quotients
        D e hn hp B hB hBC hperm K P A C hAC hA hC)

/-- The outstanding intrinsic unitary condition suffices for the original
normalizer conclusion, with all source placement and inspection discharged. -/
theorem source_a5_oddPrimeNormalizer_control_of_unitary_sylow_quotients
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hunitary : SourceOddUnitarySylowQuotients.{u})
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    normalizer (B : Set G) ≤ D.maximalLocal := by
  by_contra hout
  obtain ⟨K,hK,_,_,hm,hno⟩ :=
    source_a5_oddPrimeNormalizer_unitary_without_sylow_quotients
      D e hn hp B hne hB hBC hBV hperm hout
  let : IsQuasisimple K := hK.2
  obtain ⟨P,hP⟩ := hunitary (K ⧸ center K) IsQuasisimple.simple hm
  exact hno P hP

/-- The original full-Hall witness is faithful from the same intrinsic
unitary condition; the original actor and ambient Hall image are retained. -/
theorem source_a5_hstar_hall_faithful_of_unitary_sylow_quotients
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hunitary : SourceOddUnitarySylowQuotients.{u})
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hcoords : SourceA5OriginalBoundedSeparatedCoordinates D e hn ht htn)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    ∃ B : Subgroup H, B ≤ D.maximalLocal.subgroupOf H ∧
      IsHallSubgroup oddPrimes (B.subgroupOf (D.maximalLocal.subgroupOf H)) ∧
      B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) = ⊥ := by
  apply source_a5_hstar_hall_faithful_of_component_normalizer_control
    D e hn ht htn hcoords _ hH hlarge
  intro p hprime hp B hne hBe hBC hBV hperm
  let : Fact p.Prime := ⟨hprime⟩
  let := hBe
  exact source_a5_oddPrimeNormalizer_control_of_unitary_sylow_quotients
    D e hn hunitary hp B hne (IsElementaryAbelian.isPGroup p B) hBC hBV hperm

/-- The original separated source has generation parameter at most two
once the two remaining intrinsic unitary conditions are proved. -/
theorem source_a5_hstar_generation_bound_of_unitary_sylow_quotients
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hunitary : SourceOddUnitarySylowQuotients.{u})
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    generationParameter H ≤ 2 := by
  apply source_a5_hstar_generation_bound_of_component_normalizer_control
    D e hn ht htn hD hbound hsep _ hH
  intro p hprime hp B hne hBe hBC hBV hperm
  let : Fact p.Prime := ⟨hprime⟩
  let := hBe
  exact source_a5_oddPrimeNormalizer_control_of_unitary_sylow_quotients
    D e hn hunitary hp B hne (IsElementaryAbelian.isPGroup p B) hBC hBV hperm
end CFSG.Quasithin.Chapter10
