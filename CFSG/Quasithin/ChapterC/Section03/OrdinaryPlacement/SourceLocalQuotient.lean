module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.PerfectTwoNormalizer
public import Theory.AtlasPort.LinearGroups.G2.PerfectTwoNormalizer
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SL3Local

/-!
# The literal local quotient in the ordinary C.3 branch

After C.3.2–C.3.4, the original conjugate span lies in the ordinary
component and normalizes its noncentral intersection with the radical.
The component center is its two-core. Passing through that exact central
quotient therefore gives a perfect subgroup normalizing a nontrivial
two-subgroup, and preserves every odd prime rank of the original span.

The concrete binary symplectic, G₂, and degree-three linear normalizer
bounds now apply to this source quotient. No normality of the original
component in the local subgroup is assumed.

Source: Aschbacher–Smith, C.3.5, printed p.150.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- The actual central quotient retains the radical normalizer geometry
and the odd prime ranks of the original source span. -/
theorem ordinary_quotient_local_data
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) :
    let A := ((conjugateSpanBy L M).subgroupOf H).subgroupOf K
    let P := (R.subgroupOf H).subgroupOf K
    let q := QuotientGroup.mk' (center K)
    Group.IsPerfect (A.map q) ∧ IsPGroup 2 (P.map q) ∧ P.map q ≠ ⊥ ∧
      A.map q ≤ normalizer (P.map q : Set (K ⧸ center K)) ∧
      ∀ p : ℕ, p.Prime → Odd p → primeRank p (A.map q) = primeRank p (conjugateSpanBy L M) := by
  let A := ((conjugateSpanBy L M).subgroupOf H).subgroupOf K
  let P := (R.subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  have hAH := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let a : A ≃* conjugateSpanBy L M :=
    (subgroupOfEquivOfLe (h.ordinary_span_le K hK)).trans (subgroupOfEquivOfLe hAH)
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk',hz]
    exact pCore_isPGroup
  have hAN : A ≤ normalizer (P : Set K) := by
    intro x hx r
    exact h.span_normalizes_radical hx ((r : H) : G)
  refine ⟨Group.IsPerfect.map q,h.radical_isTwoGroup.comap_subtype.comap_subtype.map q,?_,
    (map_mono hAN).trans (P.le_normalizer_map q),?_⟩
  · intro he
    have hc : P ≤ center K := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff P).mp he
    apply h.ordinary_radical_intersection_not_centralizes K hK
    intro r hr k hk
    exact congrArg (fun x : K => (x : H))
      (mem_center_iff.mp (hc (show (⟨r,hr.2⟩ : K) ∈ P from hr.1)) ⟨k,hk⟩)
  · intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho q hk A).trans
      (primeRank_congr p a)

/-- Transfer a concrete normalizer bound through the literal component quotient. -/
theorem ordinary_span_primeRank_le_of_model_two_normalizers
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    {S : Type*} [Group S] [Finite S] (e : K ⧸ center K ≃* S)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hlocal : ∀ A P : Subgroup S, Group.IsPerfect A → IsPGroup 2 P → P ≠ ⊥ →
      A ≤ normalizer (P : Set S) → primeRank p A ≤ 1) :
    primeRank p (conjugateSpanBy L M) ≤ 1 := by
  obtain ⟨hA,hP,hne,hn,hr⟩ := h.ordinary_quotient_local_data K hK
  let A := (((conjugateSpanBy L M).subgroupOf H).subgroupOf K).map
    (QuotientGroup.mk' (center K))
  let P := ((R.subgroupOf H).subgroupOf K).map (QuotientGroup.mk' (center K))
  let := hA
  have hbe : P.map e.toMonoidHom ≠ ⊥ := fun he => hne
    ((map_eq_bot_iff_of_injective P e.injective).mp he)
  have hb := hlocal (A.map e.toMonoidHom) (P.map e.toMonoidHom)
    (Group.IsPerfect.map _) (hP.map _) hbe
    ((map_mono hn).trans (P.le_normalizer_map e.toMonoidHom))
  rw [←hr p (Fact.out) ho]
  exact (primeRank_congr p (e.subgroupMap A)).le.trans hb

/-- The binary symplectic row has source span of odd prime rank at most one. -/
theorem ordinary_span_primeRank_le_one_of_sp4
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (conjugateSpanBy L M) ≤ 1 := by
  apply h.ordinary_span_primeRank_le_of_model_two_normalizers K hK e ho
  intro A P hA hP hne hn
  let := hA
  by_contra! hb
  apply Theory.SpecificGroups.SymplecticFour.no_perfect_odd_rank_two_in_two_normalizer
    P hP hne ho (by omega) A.subtype A.subtype_injective
  simpa only [range_subtype] using hn

/-- The binary G₂ row has source span of odd prime rank at most one. -/
theorem ordinary_span_primeRank_le_one_of_g2
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* Atlas.G2.Model F) (hq : 2 < Nat.card F)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (conjugateSpanBy L M) ≤ 1 := by
  apply h.ordinary_span_primeRank_le_of_model_two_normalizers K hK e ho
  intro A P hA hP hne hn
  let := hA
  exact Atlas.G2.PerfectSubgroups.perfect_subgroup_two_normalizer_odd_rank_le_one
    P hP hne hq A hn ho
/-- The binary projective degree-three row has source span of five-rank
at most one, including the field of order two. -/
theorem ordinary_span_fiveRank_le_one_of_psl3
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : K ⧸ center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :
    primeRank 5 (conjugateSpanBy L M) ≤ 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply h.ordinary_span_primeRank_le_of_model_two_normalizers K hK e (by decide)
  intro A P hA hP hne hn
  let := hA
  by_contra! hb
  apply OrdinaryPlacement.SL3Local.no_perfect_five_rank_two_in_two_normalizer
    P hP hne (by omega) A.subtype A.subtype_injective
  simpa only [range_subtype] using hn

end CFSG.Quasithin.ChapterC.HypothesisC28
