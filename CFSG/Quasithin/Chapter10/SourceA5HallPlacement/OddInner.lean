module

public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PairSylow
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.PlacedComplete
public import Theory.SpecificGroups.OddClassicalSylowFrattini
public import Theory.GroupTheory.SylowFrattiniBounds

/-!
# Inner action on the odd classical Hall components

Lift the actual Sylow subgroup of the projective central quotient through
its SL, SU or Sp cover. The natural action has dimension at most four, so
its Frattini quotient has order at most 128. The original pair's Sylow
restriction forces inner residual action and the completed placed-component
inspection excludes every odd classical row. Only the G₂ row remains in
the odd Theorem B inspection.

Source: Aschbacher–Smith 4.4.10–12, printed pp.621–622.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04 ChapterA.Section02 ClassificationModels
open Theory.SpecificGroups.OddClassicalSylowFrattini
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The six odd classical rows supply inner action on the literal normal cover. -/
theorem source_a5_oddNormalizer_inner_of_odd_classical
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G))) [K.Normal] [IsQuasisimple K]
    (hmodel :
      (∃ n q : ℕ, n ≤ 4 ∧ Odd q ∧ ClassicalGroup.IsPSL (K ⧸ center K) n q) ∨
      (∃ n q : ℕ, n ≤ 4 ∧ Odd q ∧ ClassicalGroup.IsPSU (K ⧸ center K) n q) ∨
      (∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSp (K ⧸ center K) 2 q)) :
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf (normalizer (B : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (B : Set G))) := by
  let P : Sylow 2 (K ⧸ center K) := Classical.choice inferInstance
  apply source_a5_oddNormalizer_inner_of_smallFrattini D e hn hp B hB hBC hperm K P
  rcases hmodel with ⟨n,q,hn,ho,hm⟩ | ⟨n,q,hn,ho,hm⟩ | ⟨q,ho,hm⟩
  · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
    rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr
      (a.subgroupMap (P : Subgroup (K ⧸ center K)))]
    exact psl_card_le_128 hn
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho
        (by simpa using hF)) Q
  · obtain ⟨F,_,_,J,hF,_hconj,⟨a⟩⟩ := hm
    let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
    rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr
      (a.subgroupMap (P : Subgroup (K ⧸ center K)))]
    exact psu_card_le_128 J hn
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hF) Q
  · obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    let Q := P.mapSurjective (f := a.toMonoidHom) a.surjective
    rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr
      (a.subgroupMap (P : Subgroup (K ⧸ center K)))]
    exact psp_four_card_le_128
      (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho
        (by simpa using hF)) Q

/-- No odd classical row occurs in the original selected Hall component. -/
theorem source_a5_oddNormalizer_no_odd_classical_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hmodel :
      (∃ n q : ℕ, n ≤ 4 ∧ Odd q ∧ ClassicalGroup.IsPSL (K ⧸ center K) n q) ∨
      (∃ n q : ℕ, n ≤ 4 ∧ Odd q ∧ ClassicalGroup.IsPSU (K ⧸ center K) n q) ∨
      (∃ q : ℕ, Odd q ∧ ClassicalGroup.IsPSp (K ⧸ center K) 2 q)) : False := by
  let : K.Normal := source_a5_oddNormalizer_component_normal
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
  let : IsQuasisimple K := hK.2
  exact source_a5_oddNormalizer_no_inner_component
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
    (source_a5_oddNormalizer_inner_of_odd_classical D e hn hp B hB hBC hperm K hmodel)

/-- The complete odd catalogue now reduces to its single exceptional G₂ row,
with the original prime-field marking. -/
theorem source_a5_oddNormalizer_odd_component_g2
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))))
    (hmodel : IsTheoremBOddModel (K ⧸ center K)) :
    ∃ r : ℕ, r.Prime ∧ Odd r ∧ IsG2At (K ⧸ center K) r := by
  have hno := source_a5_oddNormalizer_no_odd_classical_component
    D e hn hp B hne hB hBC hBV hperm K hK houtK hFK
  cases hmodel with
  | linear_two q ho hm => exact (hno (.inl ⟨2,q,by decide,ho,hm⟩)).elim
  | linear_three r f _ ho _ hm => exact (hno (.inl ⟨3,r^f,by decide,ho.pow,hm⟩)).elim
  | unitary_three r f _ ho _ hm =>
    exact (hno (.inr (.inl ⟨3,r^f,by decide,ho.pow,hm⟩))).elim
  | symplectic r _ ho hm => exact (hno (.inr (.inr ⟨r,ho,hm⟩))).elim
  | g2 r hr ho hm => exact ⟨r,hr,ho,hm⟩
  | linear_four r _ hf hm =>
    have ho : Odd r := by
      obtain ⟨k,rfl⟩ := hf
      exact (even_two.pow_of_ne_zero (by positivity)).add_one
    exact (hno (.inl ⟨4,r,le_rfl,ho,hm⟩)).elim
  | unitary_four s hs hmers hm =>
    have ho : Odd s := by
      obtain ⟨b,hb⟩ := hmers
      have hb0 : b ≠ 0 := by
        intro he
        simp only [he,pow_zero] at hb
        have := hs.two_le
        omega
      have heven : Even (s+1) := hb.symm ▸ even_two.pow_of_ne_zero hb0
      exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp heven)
    exact (hno (.inr (.inl ⟨4,s,le_rfl,ho,hm⟩))).elim

end CFSG.Quasithin.Chapter10
