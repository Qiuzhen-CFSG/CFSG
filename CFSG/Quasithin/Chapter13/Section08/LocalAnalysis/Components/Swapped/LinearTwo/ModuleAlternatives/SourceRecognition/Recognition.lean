module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.FullOrbit
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Tensor

/-!
# The original exchanged field-four module alternatives

The literal source maximal quotient is faithful and irreducible, with zero
fixed spaces for both components. Its original F.9 quadratic actor supplies
a cubic bound of two. Homogeneous orbit classification makes its restriction
to the component product irreducible. The actual exchange then recognizes
the entire quotient as the natural orthogonal module.

The previously proved non-FF and commuting-cubic central-cover arguments
recover the whole original U_H/V₁, including its group equivalence and
intertwining linear equivalence. The resulting alternatives are applied to
`Original.orthogonal_of_module_alternatives`; no classification callback or
model-identification premise remains. The final geometric contradiction is
owned by the original source assembly.

Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953; D.3.5 and D.3.7,
pp.195–199; F.9.18, pp.325–326.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open F918Sections.NoStrong

/-- The cubic bound forces a faithful component product to act irreducibly
on an irreducible ambient exchanged module. -/
theorem irreducible_component_orbit
    {D F U : Type*} [Group D] [Finite D] [Field F] [Finite F] [CharP F 2]
    (a : ExchangedActor KnownSimple.IsKnownSimple D F 2)
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (σ : Representation (ZMod 2) D U) [σ.IsIrreducible]
    (hσ : Function.Injective σ)
    (ha : fixedSpace σ a.component = ⊥) (hb : fixedSpace σ a.second = ⊥)
    (hc : cubicRatio σ ≤ 2) : IsIrreducible (σ.comp a.orbit.subtype) := by
  let : a.orbit.Normal := a.orbit_normal
  obtain ⟨I,hI,hspan,hirr,hfaith⟩ := exists_full_sylow_constituent a σ ha hb
  let := hirr
  have hz : fixedSpace σ a.orbit = ⊥ := by
    apply bot_unique
    apply le_trans _ ha.le
    intro u hu c
    exact hu ⟨c,a.component_le c.property⟩
  obtain ⟨e,_,_,_,_⟩ := exchanged_product_coordinates a σ
  have htop := homogeneous_constituent_eq_top σ hσ hI hz hspan hfaith e hc
  subst I
  let b : RepEquiv (invariantSubspace σ a.orbit ⊤ hI.invariant).toRepresentation
      (σ.comp a.orbit.subtype) :=
    RepEquiv.mk (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) U) ≃ₗ[ZMod 2] U)
      (fun _ => rfl)
  exact (RepEquiv.irreducible_euqiv b).mp hirr

/-- The intrinsic field-four recognition includes the entire original carrier. -/
theorem exchanged_cubic_orthogonal
    {D F U : Type*} [Group D] [Finite D] [Field F] [Finite F] [CharP F 2]
    (a : ExchangedActor KnownSimple.IsKnownSimple D F 2)
    [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (σ : Representation (ZMod 2) D U) [σ.IsIrreducible]
    (hσ : Function.Injective σ)
    (ha : fixedSpace σ a.component = ⊥) (hb : fixedSpace σ a.second = ⊥)
    (hc : cubicRatio σ ≤ 2) : HasOrthogonalFourOrbit σ a.orbit := by
  let := irreducible_component_orbit a σ hσ ha hb hc
  exact orthogonal_of_irreducible_restriction a σ hσ hc

open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
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
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving


/-- Original source hypotheses give the whole-module orthogonal alternative.
The chosen quotient is recognized intrinsically; the existing central-cover
and non-FF arguments lift its coordinates to the entire U_H/V₁ carrier. -/
theorem source_whole_orthogonal {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G)) :
    HasOrthogonalFourOrbit ρ
      (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) := by
  obtain ⟨W,hW,hirr,hfaith,_,hlift,B,_,_,hB,_⟩ := exists_source_constituent_reduction
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn
  let := hirr
  apply hlift
  obtain ⟨ha,hb⟩ := source_irreducible_quotient_component_fixed_eq_bot
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn W hW
  obtain ⟨F,hF,hfin,hchar,a,hfirst,hsecond,horbit,_⟩ := exists_source_exchangedActor
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ht htn
  rw [←hfirst] at ha
  rw [←hsecond] at hb
  rw [←horbit]
  exact exchanged_cubic_orthogonal a W.quotientRepresentation hfaith ha hb
    ((cubicRatio_le_nat_iff _ 2).mpr ⟨Source.starImage H B,hB.1,
      isCubic_of_isQuadratic hB.2.1,hB.2.2⟩)

/-- The requested literal alternatives in 13.8.16(1). The original placement
and diagonal hypotheses eliminate the cross-factor branch and force the
actual whole-module orthogonal identification. -/
theorem source_module_alternatives {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G)) :
    HasCrossFactorQuotient ρ (Source.starImage H K) (Source.starImage H (K.conjBy t)) ∨
      HasOrthogonalFourOrbit ρ (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) :=
  Or.inr (source_whole_orthogonal d h hF9all hcentral hcomm hsource
    hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn)

/-- Literal application of the proved alternatives to the original assembly
interface; the final geometric contradiction belongs to the source owner. -/
theorem source_recognition {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G)) :
    HasOrthogonalFourOrbit ρ
      (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) :=
  Original.orthogonal_of_module_alternatives d h hF9all hcentral hcomm hsource
    hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn
    (source_module_alternatives d h hF9all hcentral hcomm hsource
      hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
