module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Orbit
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.Original
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.Theta
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ThreeResidualOrbit
public import Theory.SpecificGroups.ProjectiveLinearThree

/-!
# The original cubic residual in the exchanged PSL₂ branch

The original solvable exclusion and Fitting calculation give the relative
index-two component normalizer. The actual PSL₂(2ⁿ) quotient supplies a
simple two-core quotient with order divisible by three. The flag involution
places H inside its strongly quasithin centralizer. Applying 1.2.2(a) inside
H and transporting through H.subtype identifies O^{3′}(H) with the literal
T-conjugate span of K. No residual equality or rank bound is an input.

The explicit earlier inputs are the original maximal-local hypothesis,
F.9 applicability, the two 13.5.4 statements, and universal 13.3.9. Their
ultimate source discharge remains with the component-normality assembly.
Source: Aschbacher--Smith, 1.2.2(a), printed p.504, and 13.8.16(1), p.952.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.Original
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)

include d h hF9all hcentral hcomm hsource hH hKH hK hmoving in
theorem moving_index : (normalizer (K.subgroupOf H : Set H)).index = 2 := by
  rcases SolvableSource.source_component_orbit d hF9all
    (SolvableSource.covered_normalizer_source d h) hcentral hcomm hsource hH K hK with hn | hi
  · exact (hmoving (conjugateSpan_eq_of_normal H K T hKH
      (le_sup_right.trans hH.1.2) hn)).elim
  · exact hi

include d h hF9all hcentral hcomm hsource hH hKH hK hmoving in
theorem threeResidual {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n)) :
    (primeToResidual 3 H).map H.subtype = conjugateSpanBy K (T : Subgroup G) := by
  have hi := moving_index d h hF9all hcentral hcomm hsource hH hKH hK hmoving
  let e : ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) ≃* Source.starImage H K :=
    cComponentTwoCoreQuotientEquiv hK
  have hm : ClassicalGroup.IsPSL ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) 2 (2 ^ n) :=
    hmodel.of_mulEquiv e
  let := (SolvableSource.component_fitting_source d h hF9all hcentral hcomm hsource hH K hK).2
  let : IsQuasisimple ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv e.symm
  have hsimple : IsSimpleGroup ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) := by
    obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hm
    have hlarge : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (n := 2) (by decide) hn
    let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
    exact f.isSimpleGroup
  let := hsimple
  have hd : 3 ∣ Nat.card ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) := by
    obtain ⟨F, _, _, _, ⟨f⟩⟩ := hm
    rw [Nat.card_congr f.toEquiv]
    exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F 2 le_rfl
  obtain ⟨z, hz, _, _, _, hG⟩ := LocalFitting.line_involution d
  have hr : primeRank 3 H ≤ 2 :=
    ((d.counterexample.qtke.toIsQTKE.involution_centralizer_stronglyQuasithin hz).of_injective
      (inclusion (hH.2.1.trans hG)) (inclusion_injective (hH.2.1.trans hG)))
        3 Nat.prime_three (by decide)
  have he := Chapter1.Section02.nonnormal_component_threeResidual hK hi hd hr
    (.linear_even n hn hm)
  have he' := congrArg (map H.subtype) he
  rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le hKH, ← MonoidHom.range_eq_map, range_subtype] at he'
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  obtain ⟨t, ht, htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  rw [he', orbit_eq_two_conjugates H K H hKH le_rfl hi
    (hTH ht) htn,
    orbit_eq_two_conjugates H K T hKH (le_sup_right.trans hH.1.2) hi ht htn]

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.Original
