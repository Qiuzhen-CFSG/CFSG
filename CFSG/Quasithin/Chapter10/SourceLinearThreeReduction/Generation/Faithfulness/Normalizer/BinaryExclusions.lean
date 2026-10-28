module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.QuotientGeometry
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectTwoNormalizer
public import Theory.AtlasPort.LinearGroups.G2.PerfectTwoNormalizer
public import Theory.SpecificGroups.Triality.PerfectTwoNormalizer
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SL3Local
public import Theory.GroupTheory.PrimeRankSquareFree

/-!
# Binary rank-two exclusions for the original nonnormal Hall residual

A nontrivial perfect component quotient has an odd prime divisor. Both
copies of that quotient survive in the actual fixed residual and in its
image in K/Z(K). The original full module gives a nonidentity two-subgroup
normalized by that perfect image. The proved parabolic bounds for binary
PSL₃, Sp₄, G₂ and triality permit odd rank at most one, a contradiction.

These are actual model exclusions with no A₅ marking. Residual placement
is the explicit earlier premise; module fixation, covering uniqueness,
inner action and the remaining model rows stay with the same assembly
owner qt-d-10-nona5-hall-faithfulness.
Source: Aschbacher--Smith 4.4.12, printed pp.621--622, used in 10.2.3(2).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
  (K : Subgroup (normalizer (B : Set G)))
  (hFK : ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
        (normalizer (B : Set G)) ≤ K)
include D hn hBC hodd hBV hFK

/-- A perfect local odd-rank-one bound excludes the actual containing component. -/
theorem source_nonnormal_oddNormalizer_no_component_of_local_rank_bound
    {S : Type*} [Group S] [Finite S] (a : K ⧸ center K ≃* S)
    (hlocal : ∀ A Q : Subgroup S, Group.IsPerfect A → IsPGroup 2 Q → Q ≠ ⊥ →
      A ≤ normalizer (Q : Set S) →
      ∀ p : ℕ, p.Prime → Odd p → primeRank p A ≤ 1) : False := by
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  let P := (F.subgroupOf K).map (QuotientGroup.mk' (center K))
  let W := ((D.fullModule.subgroupOf N).subgroupOf K).map (QuotientGroup.mk' (center K))
  obtain ⟨hP,hW,hE,_,hN,hr⟩ :=
    source_nonnormal_oddNormalizer_component_quotient_geometry D hn B hBC hodd hBV K hFK
  let : Group.IsPerfect P := hP
  let : IsElementaryAbelian 2 W := hE
  let A := P.map a.toMonoidHom
  let Q := W.map a.toMonoidHom
  have hQ : Q ≠ ⊥ := fun he => hW ((map_eq_bot_iff_of_injective W a.injective).mp he)
  have hAQ : A ≤ normalizer (Q : Set S) :=
    (map_mono hN).trans (W.le_normalizer_map a.toMonoidHom)
  obtain ⟨p,hp,ho,hd⟩ := source_component_quotient_has_odd_prime D
  let : Fact p.Prime := ⟨hp⟩
  have hl := hlocal A Q (Group.IsPerfect.map a.toMonoidHom)
    ((IsElementaryAbelian.isPGroup 2 W).map _) hQ hAQ p hp ho
  have heq : primeRank p A = 2 * primeRank p (L ⧸ pCore 2 L) := by
    change primeRank p (P.map a.toMonoidHom) = _
    rw [←primeRank_congr p (P.equivMapOfInjective a.toMonoidHom a.injective)]
    exact hr p hp ho
  have hpos : primeRank p (L ⧸ pCore 2 L) ≠ 0 :=
    fun h => PrimeRank.eq_zero_iff_not_dvd_card.mp h hd
  omega

/-- The actual binary projective-linear-three row cannot contain the fixed residual. -/
theorem source_nonnormal_oddNormalizer_no_placed_psl3_component
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (a : K ⧸ center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) E) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_local_rank_bound
    D hn B hBC hodd hBV K hFK a
  intro A Q hA hQ hne hN p hp ho
  let := hA
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨n,_,hcard⟩ := FiniteField.card E 2
  have hE : Nat.card E = 2 ^ (n : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  by_cases hn1 : (n : ℕ) = 1
  · have hcardE : Nat.card E = 2 := by simpa only [hn1,pow_one] using hE
    apply (_root_.primeRank_le_of_injective p A.subtype A.subtype_injective).trans
    apply primeRank_le_one_of_square_not_dvd
    rw [Matrix.PSL3.LinearThree.card_projective E,hcardE]
    norm_num
    intro hsq
    have hle : p ^ 2 ≤ 168 := Nat.le_of_dvd (by decide) hsq
    have hbound : p ≤ 12 := by nlinarith
    have htwo := hp.two_le
    interval_cases p <;> norm_num at *
  · obtain ⟨g,point,hg⟩ :=
      MainConverse.LinearThreeGeometry.twoLocal_conjugate_le E n.pos hE
        (normalizer (Q : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) E))) ⟨Q,hne,hQ,rfl⟩
    let j := (MulAut.conj g).toMonoidHom.comp A.subtype
    have hj : j.range ≤ Matrix.PSL3.RootPlaneGeometry.parabolic E point := by
      refine le_trans ?_ hg
      rintro _ ⟨x,rfl⟩
      exact mem_map_of_mem _ (hN x.property)
    have hfour : 4 ≤ Nat.card E := by
      rw [hE]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
        (show 2 ≤ (n : ℕ) by have := n.pos; omega)
    by_contra! hb
    apply Matrix.PSL3.LinearThree.PerfectSubgroups.no_perfect_odd_rank_two_in_parabolic
      E ho (by omega) hfour j ((MulAut.conj g).injective.comp A.subtype_injective)
    cases point
    · exact Or.inr hj
    · exact Or.inl hj

/-- The actual binary symplectic-four row cannot contain the fixed residual. -/
theorem source_nonnormal_oddNormalizer_no_placed_sp4_component
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (a : K ⧸ center K ≃* Theory.SpecificGroups.SymplecticFour.Sp E) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_local_rank_bound
    D hn B hBC hodd hBV K hFK a
  intro A Q hA hQ hne hN p hp ho
  let := hA
  let : Fact p.Prime := ⟨hp⟩
  by_contra! hb
  apply Theory.SpecificGroups.SymplecticFour.no_perfect_odd_rank_two_in_two_normalizer
    Q hQ hne ho (by omega) A.subtype A.subtype_injective
  simpa only [range_subtype] using hN

/-- The actual large binary G₂ row cannot contain the fixed residual. -/
theorem source_nonnormal_oddNormalizer_no_placed_g2_component
    {E : Type*} [Field E] [Finite E] [CharP E 2] (hE : 2 < Nat.card E)
    (a : K ⧸ center K ≃* Atlas.G2.Model E) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_local_rank_bound
    D hn B hBC hodd hBV K hFK a
  intro A Q hA hQ hne hN p hp ho
  let := hA
  let : Fact p.Prime := ⟨hp⟩
  exact Atlas.G2.PerfectSubgroups.perfect_subgroup_two_normalizer_odd_rank_le_one
    Q hQ hne hE A hN ho

/-- The actual binary triality row cannot contain the fixed residual. -/
theorem source_nonnormal_oddNormalizer_no_placed_triality_component
    (n : ℕ) (hn' : 0 < n)
    (a : K ⧸ center K ≃* Triality.Standard.Carrier
      (Triality.Standard.binaryParameters n hn')) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_local_rank_bound
    D hn B hBC hodd hBV K hFK a
  intro A Q hA hQ hne hN p hp ho
  let := hA
  let : Fact p.Prime := ⟨hp⟩
  exact Triality.Standard.PerfectTwoNormalizer.perfect_subgroup_two_normalizer_odd_rank_le_one
    n hn' Q hQ hne A hN ho

end CFSG.Quasithin.Chapter10
