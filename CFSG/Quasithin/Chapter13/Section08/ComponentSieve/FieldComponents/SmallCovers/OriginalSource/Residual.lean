module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SourceContext
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.SourceComparison
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LocalSubgroups
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels
public import Theory.GroupTheory.CComponent.SixTheta

/-!
# Original central-cover residuals and ordinary Mathieu-cover exclusion

The preceding solvable-overgroup theorem places the nontrivial central
residual Y in L₁. Ordinary local A₆ forces Y = L₁; in the covered local
case the marked subgroup catalogue and the L₀ normalizer bound leave
Y = L₁ or Y = L₁,+. The latter direction moves the full literal U_H.

For a Mathieu triple-cover component, Y = L₁ gives H = KT. The native
hexad comparison then places a triple-A₆ C-component in H ∩ M. Its
order-three elements generate it, whereas the source theta identity puts
all of them in the solvable L₁. This contradiction excludes Y = L₁ and
thus excludes the Mathieu triple-cover row for ordinary local A₆.
Independently, A.3.18 puts L₁ in an actual six-cover component and gives
the source product and commutator conclusions for that row.

The field-sieve owner qt-d-138-fields-source retains the remaining cover
exclusions and their literal V_H/U_H permutation obstruction. The final
owner qt-d-1381-source supplies the earlier SourceContext. No full
13.8.21 exclusion or unrestricted-overgroup reduction is asserted here.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.21(2), printed p.956 (PDF p.973), using 13.8.13 and A.3.18.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open Reduction Reduction.LocalGeometry Reduction.LocalGeometry.CoverParabolics
open SourceCompletion LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
private theorem component_le (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K) : K ≤ H :=
  (le_sup_left.trans le_sup_left).trans_eq c.component.generated

theorem source_residual_located
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3) :
    coverResidualIn K ≠ ⊥ ∧ coverResidualIn K ≤ one L T V₁ := by
  let := c.component.normal
  let := LocalFitting.local_solvable c.localSetup
  exact coverResidualIn_located H K (one L T V₁) T G₁ M (component_le c)
    c.component.local_overgroup.1.2 c.component.local_overgroup.2.1 hc c.component.theta
    (SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339)

theorem source_residual_eq_one_of_ordinary
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    coverResidualIn K = one L T V₁ := by
  let := c.component.normal
  exact coverResidualIn_eq_of_prime_L1 H K (one L T V₁) (component_le c)
    (le_sup_left.trans c.component.local_overgroup.1.2) (source_residual_located c hc).2
    hc (residual_isPPerfect _) (LocalFitting.ordinary_core_card c.localSetup ⟨eL⟩)

/-- The actual central residual has only the two source directions. -/
theorem source_residual_alternatives
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3) :
    coverResidualIn K = one L T V₁ ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
        coverResidualIn K = plus L T V₁ := by
  classical
  let := c.component.normal
  by_cases he : coverResidualIn K = one L T V₁
  · exact Or.inl he
  right
  have hy := source_residual_located c hc
  rcases local_quotient_alternatives c.localSetup with ⟨e,_⟩ | ⟨e,_⟩
  · exact (he (source_residual_eq_one_of_ordinary c hc e)).elim
  · refine ⟨⟨e⟩, ?_⟩
    have hn := normalizes_coverResidualIn H K (component_le c)
    rcases Section07.ModelExclusions.covered_proper_point_subgroup
      (localNaturalSetup c.localSetup) ⟨e⟩ (lt_of_le_of_ne hy.2 he) hy.1
      (coverResidualIn_isPPerfect K)
      ((le_sup_right.trans c.component.local_overgroup.1.2).trans hn) with hz | hp
    · rw [hz] at hn
      exact (c.component.local_overgroup.2.2 (hn.trans
        (SolvableSource.covered_normalizer_source c.localSetup c.maximal ⟨e⟩))).elim
    · exact hp

/-- The proper direction fully moves the literal source numerator. -/
theorem source_proper_residual_generates
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hc : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (hne : coverResidualIn K ≠ one L T V₁) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      coverResidualIn K = plus L T V₁ ∧
      Source.UH H V₃ = ⁅Source.UH H V₃, coverResidualIn K⁆ := by
  let := c.component.normal
  rcases source_residual_alternatives c hc with he | ⟨he,hp⟩
  · exact (hne he).elim
  refine ⟨he,hp,UH_eq_commutator_coverResidual H K V₃ (component_le c) ?_⟩
  rw [hp]
  exact (Section07.ModelExclusions.seed_commutator_plus
    (localNaturalSetup c.localSetup) he).symm

private theorem no_cover_component_in_overlap
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (J : Subgroup G) (hJ : J ∈ Chapter1.cComponentsIn (H ⊓ M))
    (hc : SolvableExclusion.IsTripleCoverSix (J ⧸ pCore 2 J)) : False := by
  let e0 : J.subgroupOf (H ⊓ M) ≃* J := subgroupOfEquivOfLe hJ.1
  let := hJ.2.perfect
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := e0.toMonoidHom) e0.surjective
  let : IsQuasisimple (J ⧸ pCore 2 J) := hc.1
  obtain ⟨e⟩ := Components.CoverModels.a6Triple_nonempty_mulEquiv
    ⟨hc.1,⟨mulEquivOfPrimeCardEq hc.2.1 (Nat.card_zmod 3)⟩,hc.2.2⟩
  have hr : 2 ≤ primeRank 3 J := by
    have hh : 2 ≤ primeRank 3 (J ⧸ pCore 2 J) := by
      rw [primeRank_congr 3 e]
      exact Representation.Hexacode.two_le_primeRank_even
    exact hh.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)
  have hz : primeRank 3 (center (J ⧸ pCore 2 J)) ≤ 1 := by
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    apply primeRank_le_of_card_le_prime_pow (n := 1)
    rw [hc.2.1]
    decide
  have hg := cubic_closure_eq_top_of_twoCore_quasisimple hr hz
  have hj : J ≤ one L T V₁ := by
    have hm := congrArg (map J.subtype) hg
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype] at hm
    rw [←hm, c.component.theta]
    apply Subgroup.closure_mono
    rintro x ⟨y,hy,rfl⟩
    exact ⟨hJ.1 y.property,(J.orderOf_coe y).trans hy⟩
  let := LocalFitting.local_solvable c.localSetup
  have hjT : J ≤ one L T V₁ ⊔ (T : Subgroup G) := hj.trans le_sup_left
  have hs : Group.IsSolvable (J.subgroupOf (H ⊓ M)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (inclusion hjT).comp e0.toMonoidHom)
      ((inclusion_injective hjT).comp e0.injective)
  exact hJ.2.not_isSolvable hs

private def centralQuotient {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)

/-- The whole-residual branch gives H=KT before any field sieve is used. -/
theorem source_product_of_residual_eq_one
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (he : coverResidualIn K = one L T V₁) : H = K ⊔ (T : Subgroup G) := by
  have hle : one L T V₁ ≤ K := he ▸ coverResidualIn_le K
  rw [←c.component.generated,sup_eq_left.mpr hle]

/-- A Mathieu triple cover cannot have its central residual equal to L₁.
The native hexad comparison would put a cubic-generated nonsolvable
C-component inside the solvable theta of H∩M. -/
theorem source_mathieu_cover_residual_ne_one
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Components.Models.M22Triple) :
    coverResidualIn K ≠ one L T V₁ := by
  intro he
  let := c.component.normal
  have hH := c.component.local_overgroup
  have hKH := component_le c
  let : IsQuasisimple (Source.starImage H K) :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 hH K c.component.component).2
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (Components.componentStarEquiv H K hKH c.component.component).symm
  have hc : Nat.card (center (K ⧸ pCore 2 K)) = 3 :=
    (Nat.card_congr (centerCongr eK).toEquiv).trans Components.CoverModels.m22Triple_center_card
  let e := (centralPreimageQuotientEquiv (pCore 2 K)).trans
    ((centralQuotient eK).trans Components.CoverModels.m22Triple_quotientCenterEquiv)
  have ht : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype (le_sup_right.trans hH.1.2),map_subgroupOf_eq_of_le (le_sup_right.trans hH.1.2)⟩
  have hTM : (T : Subgroup G) ≤ M := by
    rw [c.localSetup.local_normalizer]
    exact c.localSetup.normalizes_L
  have hproper : H ⊓ M < H := lt_of_le_of_ne inf_le_left
    (fun hh => hH.2.2 (hh.ge.trans inf_le_right))
  have hspan := solvableOvergroupSpan_le_overlap H K (one L T V₁) T G₁ M hH.2.1 he
    (SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339)
  obtain ⟨s,_,hs,hj⟩ := mathieu_source_component_comparison H K T (H ⊓ M)
    hH.1.1 hKH (source_product_of_residual_eq_one c he) ht e hc hproper
    (le_inf (le_sup_right.trans hH.1.2) hTM) hspan
  exact no_cover_component_in_overlap c s.subgroup hj hs

/-- Both local alternatives reduce a Mathieu triple cover to the proper
plus residual and fully moved source numerator, without a residual premise. -/
theorem source_mathieu_cover_residual
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Components.Models.M22Triple) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      coverResidualIn K = plus L T V₁ ∧
      Source.UH H V₃ = ⁅Source.UH H V₃, coverResidualIn K⁆ :=
  source_proper_residual_generates c
    ((Nat.card_congr (centerCongr eK).toEquiv).trans Components.CoverModels.m22Triple_center_card)
    (source_mathieu_cover_residual_ne_one c eK)

/-- The original ordinary local quotient excludes the Mathieu triple-cover row. -/
theorem source_no_mathieu_cover_of_ordinary
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Components.Models.M22Triple) := by
  rintro ⟨eK⟩
  exact source_mathieu_cover_residual_ne_one c eK
    (source_residual_eq_one_of_ordinary c
      ((Nat.card_congr (centerCongr eK).toEquiv).trans Components.CoverModels.m22Triple_center_card) eL)

/-- A.3.18 for the actual six-cover component puts the theta generators in K. -/
theorem source_six_cover_containment
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple) : one L T V₁ ≤ K := by
  let D := K.subgroupOf H
  let := c.component.normal
  let e := (QuotientGroup.congr (pCore 2 D) (pCore 2 K)
    (subgroupOfEquivOfLe (component_le c)) (pCore_map_iso 2 _)).trans eK
  rw [c.component.theta, Subgroup.closure_le]
  intro x hx
  let y : H := ⟨x,hx.1.1⟩
  exact HexacodeTheta.order_three_mem D c.component.component e
    (c.component.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
    ((H.orderOf_coe y).symm.trans hx.2) (le_normalizer_of_normal (mem_top y))

/-- The six-cover row supplies containment, product and full commutator
before its remaining representation-theoretic exclusion. -/
theorem source_six_cover_consequences
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Components.Models.A6Triple) :
    one L T V₁ ≤ K ∧ H = K ⊔ (T : Subgroup G) ∧
      Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ := by
  have hle := source_six_cover_containment c eK
  have hKH := component_le c
  have hn : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKH).mp c.component.normal
  refine ⟨hle, ?_, ?_⟩
  · rw [← c.component.generated, sup_eq_left.mpr hle]
  · exact (Section07.ModelExclusions.span_commutator_of_containing_normal_component
      (localNaturalSetup c.localSetup) hKH hn hle).symm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
