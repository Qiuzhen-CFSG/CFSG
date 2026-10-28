module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.ModelQuotients

/-!
# Quotient models for a relatively normal component

The component is represented inside its specified local overgroup, never
assumed subnormal in the original simple group. Transport both stages of
the two-odd quotient along the literal subgroup-of equivalence, apply
component minimality there, and transport the resulting radical quotient
back. This keeps the source's normality and quotient conventions intact.
Source: Aschbacher--Smith 11.1.1--2 and 11.4.1(3), pp.761--762,776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G] [Finite G] {N K : Subgroup G}

omit [Finite G] in
/-- Perfectness is transported from the component in its actual local overgroup. -/
theorem relative_component_perfect (hK : Source.ComponentIn N K) : Group.IsPerfect K := by
  let := hK.2.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hK.1).toMonoidHom) (subgroupOfEquivOfLe hK.1).surjective

/-- The iterated quotient and the radical quotient use their canonical maps. -/
theorem relative_radical_model_of_twoOdd_sl2 (hK : Source.ComponentIn N K)
    {p : ℕ} (hp : 3 < p) (hm : Source.IsSL (Source.TwoOddQuotient K) 2 p) :
    ClassicalGroup.IsPSL (K ⧸ solvableRadical K) 2 p := by
  let B := K.subgroupOf N
  let e : B ≃* K := subgroupOfEquivOfLe hK.1
  let e₂ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let eo := QuotientGroup.congr _ _ e₂ (pPrimeCore_map_iso 2 e₂)
  obtain ⟨F, _, _, hF, ⟨f⟩⟩ := hm
  have hmB : Source.IsSL (Source.TwoOddQuotient B) 2 p :=
    ⟨F, inferInstance, inferInstance, hF, ⟨eo.trans f⟩⟩
  obtain ⟨E, _, _, hE, ⟨g⟩⟩ := radical_model_of_twoOdd_sl2 hK.2 hp hmB
  exact ⟨E, inferInstance, inferInstance, hE,
    ⟨(QuotientGroup.congr _ _ e (map_solvableRadical_equiv e)).symm.trans g⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
