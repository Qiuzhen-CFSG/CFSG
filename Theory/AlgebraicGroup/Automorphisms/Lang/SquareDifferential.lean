module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.ZeroDifferential

/-!
# Lang surjectivity from vanishing differential of the square

For a surjective algebraic-group endomorphism whose square has zero
differential, the fixed subgroup is finite by its inclusion in the square's
fixed subgroup. Every inner twist has the same property: the square of
`Int(a) σ` is `Int(a σ(a)) σ²`. Two nonempty open Lang ranges therefore
intersect in the connected group and give every Lang solution.

This is the square-Frobenius case of Steinberg, *Endomorphisms of Linear
Algebraic Groups*, §§10.7–10.8. It applies to the actual exceptional Ree map,
including its first power; its own differential need not vanish.
-/

namespace Theory.AlgebraicGroup
open Bor1 Topology
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

private def squareLangConjugation (a : Variety.Point G) : Morphism G G where
  toVariety := conjugationByMorphism G a
  map_one := by simp [conjugationByMorphism_apply]
  map_mul := by
    intro x y
    simp only [conjugationByMorphism_apply]
    group

/-- Fixed points of an endomorphism whose square has zero differential form
a finite group, by inclusion into the fixed points of the square. -/
public theorem finite_fixed_of_square_differential_eq_zero (σ : Morphism G G)
    (hd : identityTangentMorphismLinearMap (σ.comp σ) = 0) :
    Finite {x : Variety.Point G | σ.onPoints x = x} := by
  let := finite_fixed_of_differential_eq_zero (σ.comp σ) hd
  apply Finite.of_injective (fun x : {x : Variety.Point G | σ.onPoints x = x} =>
    (⟨x.val, by change σ.onPoints (σ.onPoints x.val) = x.val; rw [x.property, x.property]⟩ :
      {x : Variety.Point G | (σ.comp σ).onPoints x = x}))
  intro x y hxy
  exact Subtype.ext (congrArg (fun z : {x : Variety.Point G | (σ.comp σ).onPoints x = x} => z.val) hxy)

/-- Every inner twist still has square-zero differential. This uses the
endomorphism identity, not the generally false product-of-nilpotent-maps rule. -/
private theorem inner_twist_square_differential_eq_zero (σ : Morphism G G)
    (hd : identityTangentMorphismLinearMap (σ.comp σ) = 0) (a : Variety.Point G) :
    identityTangentMorphismLinearMap
      (((squareLangConjugation a).comp σ).comp ((squareLangConjugation a).comp σ)) = 0 := by
  have heq : ((squareLangConjugation a).comp σ).comp ((squareLangConjugation a).comp σ) =
      (squareLangConjugation (a * σ.onPoints a)).comp (σ.comp σ) := by
    apply Morphism.ext
    funext x
    change a * σ.onPoints (a * σ.onPoints x * a⁻¹) * a⁻¹ =
      (a * σ.onPoints a) * σ.onPoints (σ.onPoints x) * (a * σ.onPoints a)⁻¹
    simp only [map_mul, map_inv]
    group
  rw [heq, identityTangentMorphismLinearMap_comp, hd, LinearMap.comp_zero]

/-- Lang surjectivity for a connected group when the square of its actual
surjective endomorphism has zero differential. -/
public theorem langMorphism_surjective_of_square_differential_eq_zero
    (σ : Morphism G G) (hsurj : Function.Surjective σ.onPoints)
    (hG : Variety.IsConnected G)
    (hd : identityTangentMorphismLinearMap (σ.comp σ) = 0) :
    Function.Surjective (langMorphism σ).toFun := by
  let : PreirreducibleSpace (Variety.Point G) :=
    ⟨(connectedAlgebraicGroup_irreducible G hG).2⟩
  have hσ : IsAlgebraicSteinbergEndomorphism σ :=
    ⟨hsurj, finite_fixed_of_square_differential_eq_zero σ hd⟩
  obtain ⟨U, hUopen, hUne, hUrange⟩ :=
    langMorphism_exists_nonempty_open_subset_range σ hσ hG
  intro a
  let τ := (squareLangConjugation a).comp σ
  have hτsurj : Function.Surjective τ.onPoints := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (a⁻¹ * y * a)
    refine ⟨x, ?_⟩
    change a * σ.onPoints x * a⁻¹ = y
    rw [hx]
    group
  have hτ : IsAlgebraicSteinbergEndomorphism τ :=
    ⟨hτsurj, finite_fixed_of_square_differential_eq_zero τ
      (inner_twist_square_differential_eq_zero σ hd a)⟩
  obtain ⟨V, hVopen, hVne, hVrange⟩ :=
    langMorphism_exists_nonempty_open_subset_range τ hτ hG
  let W := (rightMulMorphism G a⁻¹).toFun ⁻¹' V
  have hWopen : IsOpen W := hVopen.preimage (rightMulMorphism G a⁻¹).continuous
  have hWne : W.Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    refine ⟨v * a, ?_⟩
    change (v * a) * a⁻¹ ∈ V
    simpa using hv
  obtain ⟨y, hyU, hyW⟩ := nonempty_preirreducible_inter hUopen hWopen hUne hWne
  obtain ⟨b, hb⟩ := hUrange hyU
  obtain ⟨c, hc⟩ := hVrange hyW
  have hc' : c * (a * σ.onPoints c⁻¹ * a⁻¹) = y * a⁻¹ := hc
  have ha : c⁻¹ * y * σ.onPoints c = a := by
    have heq := congrArg (fun z => c⁻¹ * z * a * σ.onPoints c) hc'
    simpa [map_inv, mul_assoc] using heq.symm
  refine ⟨c⁻¹ * b, ?_⟩
  calc
    (langMorphism σ).toFun (c⁻¹ * b) =
        c⁻¹ * (langMorphism σ).toFun b * σ.onPoints c := by
          simp [langMorphism_apply, map_mul, mul_assoc]
    _ = c⁻¹ * y * σ.onPoints c := by rw [hb]
    _ = a := ha
end Theory.AlgebraicGroup
