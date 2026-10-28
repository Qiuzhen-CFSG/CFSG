module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SourceContext
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedGeneration
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms

/-!
# Original Mathieu placement and exclusion of the covered local case

The actual M₂₂ quotient is centerless, has three-rank two and has outer
order dividing two. The relative component index theorem therefore puts
every original theta generator in K, giving L₁ ≤ K. This constructs the
complete standing input to the native hexad placement, including the
original Sylow subgroup, relative normality and solvable-overgroup bound.

The resulting parabolic has three-part three. The literal component map
has a two-group kernel, so |L₁|₃ = 3. In the covered local A₆ case, the
original flag gives an order-nine quotient of L₁, a contradiction. Thus
an ordinary M₂₂ component forces the ordinary local A₆ quotient. The same
containment supplies H = KT and U_H = [U_H,K].

This removes the ordinary Mathieu row in the covered local source sieve.
The ordinary local Mathieu module exclusion and the other field/cover
branches remain with qt-d-138-fields-source. The final section owner
qt-d-1381-source supplies the preceding SourceContext.
Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973), using
A.3.18 and the original covered flag of 13.2.1–2.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
open SourceCompletion LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LinearThree.Geometry.ExternalComponentAction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

private theorem component_le (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K) : K ≤ H :=
  (le_sup_left.trans le_sup_left).trans_eq c.component.generated

/-- Every original theta generator lies in the actual Mathieu component. -/
theorem source_mathieu_containment
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) : one L T V₁ ≤ K := by
  apply RankReduction.theta_le_component_of_model_facts c.component
  · apply eq_bot_iff.mpr
    intro z hz
    have he := (centerCongr eK ⟨z,hz⟩).property
    change eK z ∈ center Sporadic.Mathieu.M22 at he
    rw [Sporadic.Mathieu.m22_center_eq_bot,mem_bot] at he
    exact eK.map_eq_one_iff.mp he
  · rw [primeRank_congr 3 eK,Sporadic.Mathieu.m22_primeRank_three]
  · rw [Nat.card_congr (MulAut.outerCongr eK).toEquiv]
    exact (by decide : Nat.Coprime 3 2).coprime_dvd_right
      Sporadic.Mathieu.M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two

/-- Construct all standing inputs to the native Mathieu placement. -/
noncomputable def sourceMathieuSetup
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) :
    Mathieu.Placement.Setup H K (one L T V₁) (T : Subgroup G) G₁ M := by
  have hH := c.component.local_overgroup
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  let := LocalFitting.local_solvable c.localSetup
  exact {
    mem_Hz := hH
    component_le := component_le c
    component := c.component.component
    component_normal := c.component.normal
    sylow_le_M := by rw [c.localSetup.local_normalizer]; exact c.localSetup.normalizes_L
    sylow := T.subtype hTH
    sylow_eq := rfl
    generated := c.component.generated.symm
    seed_le_component := source_mathieu_containment c eK
    theta := c.component.theta
    solvable := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (show one L T V₁ ≤ one L T V₁ ⊔ (T : Subgroup G) from le_sup_left))
    model := eK
    solvable_overgroups := fun X hX hLT hs =>
      SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
        c.centralizer c.noncentral_core c.earlier1339 X hLT hX hs }

/-- The actual hexad/parabolic witness, including both possible marked
parabolic classes and the literal radical map. -/
theorem source_mathieu_placement
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) :
    Nonempty (Mathieu.Placement.Witness (sourceMathieuSetup c eK)) := by
  apply (sourceMathieuSetup c eK).source_placement V₃
  · intro he
    have hc := c.localSetup.seed_card
    rw [he, card_bot] at hc
    omega
  · exact Section07.ModelExclusions.seed_commutator_point_residual (localNaturalSetup c.localSetup)

/-- The original point residual has three-part exactly three. -/
theorem source_mathieu_three_part
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) :
    3 ^ (Nat.card (one L T V₁)).factorization 3 = 3 := by
  obtain ⟨w⟩ := source_mathieu_placement c eK
  exact w.three_part

/-- An ordinary Mathieu component forces the ordinary local A₆ quotient. -/
theorem source_mathieu_ordinary
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  rcases local_quotient_alternatives c.localSetup with ⟨e,_⟩ | ⟨e,he⟩
  · exact ⟨e⟩
  · obtain ⟨a⟩ := local_covered_flag_model c.localSetup e he
    have hq := a.one_quotient_card (CoverFactorization.source_factorization a)
    have hd : 9 ∣ Nat.card (one L T V₁) := by
      rw [←hq]
      exact card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 (one L T V₁)))
        (QuotientGroup.mk'_surjective _)
    have htwo : 2 ≤ (Nat.card (one L T V₁)).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hd
    have hone : (Nat.card (one L T V₁)).factorization 3 = 1 := by
      apply Nat.pow_right_injective (by decide : 1 < 3)
      simpa only [pow_one] using source_mathieu_three_part c eK
    omega

/-- The covered local A₆ case excludes the ordinary Mathieu component. -/
theorem source_no_mathieu_of_covered
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eL : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) := by
  rintro ⟨eK⟩
  obtain ⟨e⟩ := source_mathieu_ordinary c eK
  have hc := Nat.card_congr (centerCongr (eL.symm.trans e)).toEquiv
  rw [Representation.Hexacode.even_center_card,
    alternatingGroup.center_eq_bot (by simp),card_bot] at hc
  omega

/-- The Mathieu row gives the original product and commutator conclusions
before the remaining ordinary-local representation contradiction. -/
theorem source_mathieu_consequences
    (c : SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (eK : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) :
    one L T V₁ ≤ K ∧ H = K ⊔ (T : Subgroup G) ∧
      Source.UH H V₃ = ⁅Source.UH H V₃,K⁆ := by
  have hle := source_mathieu_containment c eK
  have hn : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (component_le c)).mp c.component.normal
  refine ⟨hle, (sourceMathieuSetup c eK).eq_component_join_sylow, ?_⟩
  exact (Section07.ModelExclusions.span_commutator_of_containing_normal_component
    (localNaturalSetup c.localSetup) (component_le c) hn hle).symm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.OriginalSource
