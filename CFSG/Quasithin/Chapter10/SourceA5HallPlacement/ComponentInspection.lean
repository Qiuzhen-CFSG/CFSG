module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PlacedComplete
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.FiniteClosure
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.FiniteInnerG2
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.FiniteInnerUnitary

/-!
# Complete inspection after placement of the original Hall residual

The complete Theorem B catalogue has no component containing the original
fixed residual: the binary and finite rows reduce to the odd rows, and the
actual rank-eight lower bound excludes those too. Thus inner action on a
normal escaping component is already impossible. The last theorem applies
this inspection to the original odd actor. Its only remaining input is inner
action in PSU4 over binary fields of order at least eight and in PSU5(4).
All odd rows and both smaller PSU4 parameters are discharged.

Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, in the original
nonnormal A5 case of 10.2.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterA.Section02 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original 4.4.3 normalizer conclusion requires inner action only in
the three remaining model families. All component selection, normality,
placement and subsequent inspection are discharged internally. -/
theorem source_a5_oddPrimeNormalizer_control_of_remaining_inner
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (hinner : ∀ (K : Subgroup (normalizer (B : Set G))), K.Normal →
      IsQuasisimple K →
      (IsTheoremBOddModel (K ⧸ center K) ∨
        (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ f)) ∨
        ClassicalGroup.IsPSU (K ⧸ center K) 5 4) →
      ((solvableResidual
        (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
          (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
            (normalizer (B : Set G)) ≤
              K ⊔ centralizer (K : Set (normalizer (B : Set G)))) :
    normalizer (B : Set G) ≤ D.maximalLocal := by
  by_contra hout
  obtain ⟨K, hK, hnormal, houtK, hFK, hm⟩ :=
    source_a5_oddPrimeNormalizer_remaining_normal_component
      D e hn hp B hne hB hBC hBV hperm hout
  let : K.Normal := hnormal
  exact source_a5_oddNormalizer_no_inner_component
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK (hinner K hnormal hK.2 hm)

/-- Every escaping original odd actor has a normal component in the prime G2
or binary unitary families. All six odd classical rows and PSU4(2), PSU4(4)
are discharged. -/
theorem source_a5_oddPrimeNormalizer_remaining_exceptional_component
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
      ((solvableResidual
        (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
          (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
            (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))) ∧
      ((∃ r : ℕ, r.Prime ∧ Odd r ∧ IsG2At (K ⧸ center K) r) ∨
        (∃ f : ℕ, 3 ≤ f ∧ ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ f)) ∨
        ClassicalGroup.IsPSU (K ⧸ center K) 5 4) := by
  obtain ⟨K, hK, hnormal, houtK, hFK, hm⟩ :=
    source_a5_oddPrimeNormalizer_remaining_normal_component
      D e hn hp B hne hB hBC hBV hperm hout
  refine ⟨K, hK, hnormal, houtK, hFK, ?_⟩
  rcases hm with ho | hu
  · exact Or.inl (source_a5_oddNormalizer_odd_component_g2
      D e hn hp B hne hB hBC hBV hperm K hK houtK hFK ho)
  · rcases hu with ⟨f, hf, hu⟩ | hu
    · by_cases hlarge : 3 ≤ f
      · exact Or.inr (Or.inl ⟨f, hlarge, hu⟩)
      · let : K.Normal := hnormal
        let : IsQuasisimple K := hK.2
        have hi := source_a5_oddNormalizer_no_inner_component
          D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
        have hsmall : f = 1 ∨ f = 2 := by omega
        rcases hsmall with rfl | rfl
        · exact (hi (source_a5_oddNormalizer_inner_of_binary_unitary_four_one
            D e hn hp B hB hBC hperm K (by simpa using hu))).elim
        · exact (hi (source_a5_oddNormalizer_inner_of_binary_unitary_four_two
            D e hn hp B hB hBC hperm K (by simpa using hu))).elim
    · exact Or.inr (Or.inr hu)

/-- Every escaping original odd actor has a normal component in one of the
two remaining binary unitary families. All odd, sporadic, other binary and
small unitary rows are discharged. -/
theorem source_a5_oddPrimeNormalizer_remaining_unitary_component
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
      ((solvableResidual
        (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
          (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
            (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))) ∧
      ((∃ f : ℕ, 3 ≤ f ∧ ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ f)) ∨
        ClassicalGroup.IsPSU (K ⧸ center K) 5 4) := by
  obtain ⟨K, hK, hnormal, houtK, hFK, hm⟩ :=
    source_a5_oddPrimeNormalizer_remaining_exceptional_component
      D e hn hp B hne hB hBC hBV hperm hout
  refine ⟨K, hK, hnormal, houtK, hFK, ?_⟩
  rcases hm with ⟨r, hr, ho, hm⟩ | hu
  · let : Fact r.Prime := ⟨hr⟩
    exact (source_a5_oddNormalizer_no_odd_g2_component
      D e hn hp B hne hB hBC hBV hperm K hK houtK hFK ho hm).elim
  · exact hu

/-- The original 4.4.3 normalizer conclusion requires inner action only in
the two remaining binary unitary families. All component selection, normality,
placement and subsequent inspection are discharged internally. -/
theorem source_a5_oddPrimeNormalizer_control_of_unitary_inner
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (hinner : ∀ (K : Subgroup (normalizer (B : Set G))), K.Normal →
      IsQuasisimple K →
      ((∃ f : ℕ, 3 ≤ f ∧ ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ f)) ∨
        ClassicalGroup.IsPSU (K ⧸ center K) 5 4) →
      ((solvableResidual
        (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
          (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
            (normalizer (B : Set G)) ≤
              K ⊔ centralizer (K : Set (normalizer (B : Set G)))) :
    normalizer (B : Set G) ≤ D.maximalLocal := by
  by_contra hout
  obtain ⟨K, hK, hnormal, houtK, hFK, hm⟩ :=
    source_a5_oddPrimeNormalizer_remaining_unitary_component
      D e hn hp B hne hB hBC hBV hperm hout
  let : K.Normal := hnormal
  exact source_a5_oddNormalizer_no_inner_component
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK (hinner K hnormal hK.2 hm)

end CFSG.Quasithin.Chapter10
