module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.ComponentQuotientMarking
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SL3Local
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectTwoNormalizer
public import Theory.AtlasPort.LinearGroups.G2.PerfectTwoNormalizer
public import Theory.SpecificGroups.Triality.PerfectTwoNormalizer
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders
public import Theory.SpecificGroups.Tits.TwoLocalFifteenFree
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.RankOneComponents
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.UnitaryComponents
public import Theory.GroupTheory.PrimeRankSquareFree
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.FiniteModelTwoRank

/-!
# Binary local exclusions for the actual Hall residual

The literal residual in K/Z(K) is perfect of three- and five-rank two and
normalizes a nontrivial binary subgroup. The proved model-local rank-one
Levi bounds exclude PSL3, Sp4, G2 and triality; the fifteen-free normalizer
orders exclude Ree F4 and Tits. The quotient, residual and full module are
those of the original Hall configuration. Residual placement in K remains
explicit for the independent component-closure producer.

Source: Aschbacher--Smith4.4.12, printed pp.621--622, specialized to the
original nonnormal A5 pair of10.2.3.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_a5_oddNormalizer_no_component_of_local_rank_bound
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {S : Type*} [Group S] [Finite S] (a : K ⧸ center K ≃* S)
    {r : ℕ} [Fact r.Prime] (hr : r = 3 ∨ r = 5)
    (hlocal : ∀ A Q : Subgroup S, Group.IsPerfect A → IsPGroup 2 Q → Q ≠ ⊥ →
      A ≤ normalizer (Q : Set S) → primeRank r A ≤ 1) : False := by
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  let P := (F.subgroupOf K).map (QuotientGroup.mk' (center K))
  let W := ((D.fullModule.subgroupOf N).subgroupOf K).map (QuotientGroup.mk' (center K))
  obtain ⟨hP,hW,hE,_,hN,h3,h5⟩ :=
    source_a5_oddNormalizer_component_quotient_local_marking_of_residual_le
      D e hn B hBC hodd hBV K hFK
  let : Group.IsPerfect P := hP
  let : IsElementaryAbelian 2 W := hE
  let A := P.map a.toMonoidHom
  let Q := W.map a.toMonoidHom
  have hQ : Q ≠ ⊥ := fun he => hW ((map_eq_bot_iff_of_injective W a.injective).mp he)
  have hAQ : A ≤ normalizer (Q : Set S) :=
    (map_mono hN).trans (W.le_normalizer_map a.toMonoidHom)
  have hl := hlocal A Q (Group.IsPerfect.map a.toMonoidHom)
    ((IsElementaryAbelian.isPGroup 2 W).map _) hQ hAQ
  have heq : primeRank r A = 2 := by
    change primeRank r (P.map a.toMonoidHom) = 2
    rw [←primeRank_congr r (P.equivMapOfInjective a.toMonoidHom a.injective)]
    rcases hr with rfl | rfl <;> assumption
  omega

theorem source_a5_oddNormalizer_no_component_of_fifteen_free
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {S : Type*} [Group S] [Finite S] (a : K ⧸ center K ≃* S)
    (hfree : ∀ Q : Subgroup S, Q ≠ ⊥ → IsPGroup 2 Q →
      ¬ 15 ∣ Nat.card (normalizer (Q : Set S))) : False := by
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  let P := (F.subgroupOf K).map (QuotientGroup.mk' (center K))
  let W := ((D.fullModule.subgroupOf N).subgroupOf K).map (QuotientGroup.mk' (center K))
  obtain ⟨hP,hW,hE,_,hN,h3,h5⟩ :=
    source_a5_oddNormalizer_component_quotient_local_marking_of_residual_le
      D e hn B hBC hodd hBV K hFK
  let : Group.IsPerfect P := hP
  let : IsElementaryAbelian 2 W := hE
  let A := P.map a.toMonoidHom
  let Q := W.map a.toMonoidHom
  have hQ : Q ≠ ⊥ := fun he => hW ((map_eq_bot_iff_of_injective W a.injective).mp he)
  have hAQ : A ≤ normalizer (Q : Set S) :=
    (map_mono hN).trans (W.le_normalizer_map a.toMonoidHom)
  have hr (r : ℕ) [Fact r.Prime] (hr : r = 3 ∨ r = 5) :
      r ∣ Nat.card (normalizer (Q : Set S)) := by
    have heq : primeRank r A = 2 := by
      change primeRank r (P.map a.toMonoidHom) = 2
      rw [←primeRank_congr r (P.equivMapOfInjective a.toMonoidHom a.injective)]
      rcases hr with rfl | rfl <;> assumption
    have hb := primeRank_mono r hAQ
    by_contra hh
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
    omega
  exact hfree Q hQ ((IsElementaryAbelian.isPGroup 2 W).map _)
    ((show Nat.Coprime 3 5 by decide).mul_dvd_of_dvd_of_dvd
      (hr 3 (Or.inl rfl)) (hr 5 (Or.inr rfl)))

theorem source_a5_oddNormalizer_no_placed_psl3_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (a : K ⧸ center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) E) : False := by
  apply source_a5_oddNormalizer_no_component_of_local_rank_bound
    D e hn B hBC hodd hBV K hFK a (r := 5) (Or.inr rfl)
  intro A Q hA hQ hne hN
  let := hA
  by_contra! hb
  apply ChapterC.OrdinaryPlacement.SL3Local.no_perfect_five_rank_two_in_two_normalizer
    Q hQ hne (by omega) A.subtype A.subtype_injective
  simpa only [range_subtype] using hN

theorem source_a5_oddNormalizer_no_placed_sp4_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (a : K ⧸ center K ≃* Theory.SpecificGroups.SymplecticFour.Sp E) : False := by
  apply source_a5_oddNormalizer_no_component_of_local_rank_bound
    D e hn B hBC hodd hBV K hFK a (r := 5) (Or.inr rfl)
  intro A Q hA hQ hne hN
  let := hA
  by_contra! hb
  apply Theory.SpecificGroups.SymplecticFour.no_perfect_odd_rank_two_in_two_normalizer
    Q hQ hne (by decide : Odd 5) (by omega) A.subtype A.subtype_injective
  simpa only [range_subtype] using hN

theorem source_a5_oddNormalizer_no_placed_g2_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (a : K ⧸ center K ≃* Atlas.G2.Model E) (hq : 2 < Nat.card E) : False := by
  apply source_a5_oddNormalizer_no_component_of_local_rank_bound
    D e hn B hBC hodd hBV K hFK a (r := 5) (Or.inr rfl)
  intro A Q hA hQ hne hN
  let := hA
  exact Atlas.G2.PerfectSubgroups.perfect_subgroup_two_normalizer_odd_rank_le_one
    Q hQ hne hq A hN (by decide : Odd 5)

theorem source_a5_oddNormalizer_no_placed_triality_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    (n : ℕ) (hnn : 0 < n)
    (a : K ⧸ center K ≃* Triality.Standard.Carrier (Triality.Standard.binaryParameters n hnn)) : False := by
  apply source_a5_oddNormalizer_no_component_of_local_rank_bound
    D e hn B hBC hodd hBV K hFK a (r := 5) (Or.inr rfl)
  intro A Q hA hQ hne hN
  let := hA
  exact Triality.Standard.PerfectTwoNormalizer.perfect_subgroup_two_normalizer_odd_rank_le_one
    n hnn Q hQ hne A hN (by decide : Odd 5)

theorem source_a5_oddNormalizer_no_placed_reeF4_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {m : ℕ} (hm : 1 ≤ m) (a : K ⧸ center K ≃* ReeF4.Model m) : False := by
  exact source_a5_oddNormalizer_no_component_of_fifteen_free
    D e hn B hBC hodd hBV K hFK a
    (fun Q hne hQ => ReeF4.ConverseParabolics.normalizer_fifteen_free hm Q hne hQ)

theorem source_a5_oddNormalizer_no_placed_tits_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    (a : K ⧸ center K ≃* Tits.ParrottGroup) : False := by
  exact source_a5_oddNormalizer_no_component_of_fifteen_free
    D e hn B hBC hodd hBV K hFK a Tits.normalizer_fifteen_free


/-- The rank-one characteristic-two family is excluded using the actual
perfect projection, with inner action supplied by the literal placement. -/
theorem source_a5_oddNormalizer_no_placed_bender_component
    (_e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (_hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hm : ClassificationModels.IsBenderModel (K ⧸ center K)) : False := by
  cases hm with
  | linear f hf hm =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact source_oddNormalizer_no_sl2_component D B hBC hodd hBV K houtK a
      (hFK.trans K.le_normalizer) (hFK.trans le_sup_left)
  | unitary f hf hm =>
    exact source_oddNormalizer_no_binary_unitary_component D B hBC hodd hBV K houtK
      (by omega : 0 < f) hm (hFK.trans le_sup_left)
  | suzuki m hm a =>
    exact source_oddNormalizer_no_suzuki_component D B hBC hodd hBV K houtK hm a.some
      (hFK.trans K.le_normalizer) (hFK.trans le_sup_left)

/-- All characteristic-two rank-two rows shared with Theorem C are
excluded on the literal marked quotient. The B-only unitary rows are separate. -/
theorem source_a5_oddNormalizer_no_placed_theoremC_rankTwo_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
    {f : ℕ} (hm : ChapterA.Section02.IsTheoremCRankTwoModel (K ⧸ center K) f) : False := by
  have hr : 2 ≤ primeRank 5 (K ⧸ center K) := by
    obtain ⟨_,_,_,_,_,_,h5⟩ :=
      source_a5_oddNormalizer_component_quotient_local_marking_of_residual_le
        D e hn B hBC hodd hBV K hFK
    exact h5 ▸ primeRank_subgroup_le 5 _
  cases hm with
  | linear hf hm =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact source_a5_oddNormalizer_no_placed_psl3_component D e hn B hBC hodd hBV K hFK a
  | symplectic hf hm =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    exact source_a5_oddNormalizer_no_placed_sp4_component D e hn B hBC hodd hBV K hFK
      (a.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
  | g2 hf hm =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    apply source_a5_oddNormalizer_no_placed_g2_component D e hn B hBC hodd hBV K hFK a
    rw [hF]
    exact (show 2 < 2 ^ 2 by decide).trans_le (Nat.pow_le_pow_right (by decide) hf)
  | triality hf hm =>
    obtain ⟨a⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f hf).mp hm
    exact source_a5_oddNormalizer_no_placed_triality_component D e hn B hBC hodd hBV K hFK f hf a
  | ree_f4 m hm hf a =>
    exact source_a5_oddNormalizer_no_placed_reeF4_component D e hn B hBC hodd hBV K hFK hm a.some
  | symplectic_derived hf a =>
    let j := a.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
    have ho : ¬ 25 ∣ Nat.card (K ⧸ center K) := by
      rw [Nat.card_congr j.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    have hu := primeRank_le_one_of_square_not_dvd (p := 5) ho
    omega
  | g2_derived hf a =>
    have ho : ¬ 25 ∣ Nat.card (K ⧸ center K) := by
      rw [Nat.card_congr a.some.toEquiv, Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
      decide
    have hu := primeRank_le_one_of_square_not_dvd (p := 5) ho
    omega
  | tits hf a =>
    exact source_a5_oddNormalizer_no_placed_tits_component D e hn B hBC hodd hBV K hFK a.some

end CFSG.Quasithin.Chapter10
