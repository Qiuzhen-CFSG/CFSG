module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.Restriction
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.ZeroDifferential

/-!
# The differential route to Lang surjectivity on fixed centralizers

A zero identity differential for the ordinary Frobenius gives a zero
differential for every positive graph-field power. Compatibility with the
literal closed-centralizer inclusion then gives a zero differential for the
restricted map. The connected zero-differential Lang theorem supplies its
surjectivity, including for exponent one.

The ordinary Frobenius differential is still an explicit premise here. The
root-parameter formulas in `Geometry` must establish it before the connected
centralizer Lang contract is complete. Connectedness is the authorized input
of that contract; no regular inverse of Frobenius is used.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 10.7--10.8 and 12.5.
-/

public section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound

open Theory.AlgebraicGroup Theory.AlgebraicGroup.Bor1

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Positive graph-field powers have zero differential as soon as the
ordinary Frobenius does. -/
theorem graphFieldMorphism_differential_eq_zero_of_frobenius
    (S : Geometry K)
    (hF : identityTangentMorphismLinearMap S.frobenius = 0)
    (n : ℕ) (hn : 0 < n) :
    identityTangentMorphismLinearMap (graphFieldMorphism S n) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hcomp : graphFieldMorphism S (m + 1) =
      S.frobenius.comp (graphFieldMorphism S m) := by
    apply Morphism.ext
    funext g
    change (S.frobenius.toVariety.iterate (m + 1)).toFun
      (S.diagram.toMulEquiv g) =
        S.frobenius.toVariety.toFun
          ((S.frobenius.toVariety.iterate m).toFun (S.diagram.toMulEquiv g))
    simp only [Variety.Morphism.iterate_toFun, Function.iterate_succ_apply']
  rw [hcomp, identityTangentMorphismLinearMap_comp, hF, LinearMap.zero_comp]

/-- The closed-centralizer inclusion transfers vanishing of the ambient
differential to the restricted endomorphism. -/
theorem centralizerRestriction_differential_eq_zero_of_frobenius
    (S : Geometry K)
    (hF : identityTangentMorphismLinearMap S.frobenius = 0)
    (n : ℕ) (hn : 0 < n)
    (x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n) :
    identityTangentMorphismLinearMap (centralizerRestriction S n x) = 0 := by
  let C := fixedCentralizer S n x
  have hcomp : C.inclusion.comp (centralizerRestriction S n x) =
      (graphFieldMorphism S n).comp C.inclusion := by
    apply Morphism.ext
    funext a
    change C.inclusion.onPoints ((centralizerRestriction S n x).onPoints a) =
      (graphFieldMorphism S n).onPoints (C.inclusion.onPoints a)
    rw [centralizerRestriction_inclusion_apply, graphFieldMorphism_onPoints]
    rfl
  have hd := congrArg identityTangentMorphismLinearMap hcomp
  rw [identityTangentMorphismLinearMap_comp,
    identityTangentMorphismLinearMap_comp,
    graphFieldMorphism_differential_eq_zero_of_frobenius S hF n hn,
    LinearMap.zero_comp] at hd
  apply LinearMap.ext
  intro D
  apply identityTangentMorphismLinearMap_inclusion_injective C
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using
    LinearMap.congr_fun hd D

/-- Conditional assembly of connected-centralizer Lang surjectivity. The
remaining premise is the actual ordinary-Frobenius differential calculation;
the centralizer restriction and all other geometric inputs are discharged. -/
theorem centralizerRestriction_lang_surjective_of_frobenius_differential_eq_zero
    (S : Geometry K)
    (hF : identityTangentMorphismLinearMap S.frobenius = 0)
    (n : ℕ) (hn : 0 < n)
    (x : graphFieldFixedSubgroup S.diagram.toMulEquiv S.frobenius.onPoints n)
    (hC : Variety.IsConnected (fixedCentralizer S n x).carrierVariety) :
    Function.Surjective (langMorphism (centralizerRestriction S n x)).toFun :=
  langMorphism_surjective_of_differential_eq_zero (centralizerRestriction S n x)
    (centralizerRestriction_bijective S n x).surjective hC
    (centralizerRestriction_differential_eq_zero_of_frobenius S hF n hn x)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound
