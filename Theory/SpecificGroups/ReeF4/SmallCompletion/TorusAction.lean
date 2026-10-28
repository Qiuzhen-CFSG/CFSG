module
public import Theory.SpecificGroups.ReeF4.SmallCompletion.Weyl
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.ApartmentStabilizer.Opposition

/-!
# The marked Ree Weyl action on the native Cartan

The relative normality theorem makes each actual orbit word normalize the
full fixed torus. Restricting conjugation gives its literal torus action.
The native eighth-power relation descends to the product of these actions.
This is the model-side action used to localize the possible mixed relation
in an arbitrary completion; no completion relation is inferred here.

Source: GLS3 2.3.4(a), and Aschbacher–Smith F.4.10,16, pp.279,282.
-/

@[expose] public noncomputable section
namespace ReeF4.SmallCompletion
open Subgroup Parabolics LargeLocalSeeds SectionGeometry.BNPair
open Parabolics.Binary.FixedGeometry

/-- The actual marked reflection preserves the full native Cartan. -/
theorem reflection_mem_normalizer_fixedTorus (m : ℕ) (s : Side) :
    (reflection m s).val ∈ normalizer (fixedTorus m : Set (Model m)) := by
  have hn : ((fixedTorus m).subgroupOf (normalizerWords m)).Normal := by
    rw [←borel_inf_normalizerWords]
    exact borel_inf_normalizerWords_normal m
  exact ((normal_subgroupOf_iff_le_normalizer (fixedTorus_le_normalizerWords m)).mp hn)
    (weylLift_mem_normalizerWords m s)

/-- Restriction of the native marked conjugation to the full Cartan. -/
def torusReflection (m : ℕ) (s : Side) : MulAut (fixedTorus m) :=
  (fixedTorus m).normalizerMonoidHom
    ⟨(reflection m s).val,reflection_mem_normalizer_fixedTorus m s⟩

/-- The two restricted actions satisfy the native eighth-power relation. -/
theorem torusReflection_product_eight (m : ℕ) :
    (torusReflection m .linear * torusReflection m .suzuki)^8 = 1 := by
  rw [torusReflection,torusReflection,←map_mul,←map_pow]
  have he : ((⟨(reflection m .linear).val,reflection_mem_normalizer_fixedTorus m .linear⟩ :
      normalizer (fixedTorus m : Set (Model m))) *
      ⟨(reflection m .suzuki).val,reflection_mem_normalizer_fixedTorus m .suzuki⟩)^8 = 1 :=
    Subtype.ext (reflection_product_eight m)
  rw [he,map_one]

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped BigOperators
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.ApartmentStabilizer
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem opposition_simple_torus (m : ℕ) (i : typeF4RootPairing_base.support)
    (t : (CoefficientField m)ˣ) :
    toSplitGroup m (opposition m) * torusWord m i t *
      (toSplitGroup m (opposition m))⁻¹ = (torusWord m i t)⁻¹ := by
  have hword : toSplitGroup m (opposition m) * torusWord m i t *
      (toSplitGroup m (opposition m))⁻¹ = torusWord m (-i : F4Chevalley.Root) t := by
    change (MulAut.conj (toSplitGroup m (opposition m))) (torusWord m i t) = _
    simp only [torusWord,weylWord,map_mul,MulAut.conj_apply,opposition_conj_root]
  rw [hword]
  apply Subtype.ext
  change (torusWord m (-i : F4Chevalley.Root) t).val = (torusWord m i t).val⁻¹
  rw [torusWord_neg_simple_coe,torusWord_simple_coe,←map_inv]
  congr 1
  ext j
  by_cases hj : j = i <;> simp [integralChevalleySimpleCorootParameter,hj]

private theorem opposition_splitTorus (m : ℕ) {t : SplitGroup m} (ht : t ∈ splitTorus m) :
    toSplitGroup m (opposition m) * t * (toSplitGroup m (opposition m))⁻¹ = t⁻¹ := by
  rw [splitTorus_eq_diagonalTorus] at ht
  obtain ⟨u,hu⟩ := ht
  let a := (toSplitGroup m (opposition m)).val
  let f := (MulAut.conj a).toMonoidHom.comp (diagonalTorusHom m)
  let g := (diagonalTorusHom m).comp (invMonoidHom : TorusParameter m →* TorusParameter m)
  have hs (i : typeF4RootPairing_base.support) (t : (CoefficientField m)ˣ) :
      f (integralChevalleySimpleCorootParameter i t) =
        g (integralChevalleySimpleCorootParameter i t) := by
    have h := congrArg Subtype.val (opposition_simple_torus m i t⁻¹)
    change a * (torusWord m i t⁻¹).val * a⁻¹ = (torusWord m i t⁻¹).val⁻¹ at h
    rw [torusWord_simple_coe,inv_inv] at h
    change a * diagonalTorusHom m (integralChevalleySimpleCorootParameter i t) * a⁻¹ =
      diagonalTorusHom m ((integralChevalleySimpleCorootParameter i t)⁻¹)
    rw [map_inv]
    exact h
  have hp (s : Finset typeF4RootPairing_base.support) :
      f (∏ i ∈ s, integralChevalleySimpleCorootParameter i (u i)) =
        g (∏ i ∈ s, integralChevalleySimpleCorootParameter i (u i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => rw [Finset.prod_insert hi,map_mul,map_mul,hs,ih]
  have hprod : (∏ i, integralChevalleySimpleCorootParameter i (u i)) = u := by
    ext j
    simp [integralChevalleySimpleCorootParameter]
  have he : f u = g u := by simpa only [hprod] using hp Finset.univ
  apply Subtype.ext
  change a*t.val*a⁻¹ = t.val⁻¹
  change a*diagonalTorusHom m u*a⁻¹ = diagonalTorusHom m u⁻¹ at he
  rw [map_inv,hu] at he
  exact he

/-- The native half-turn inverts the entire fixed Cartan, including at q=8. -/
theorem reflection_product_four_inverts (m : ℕ) (t : fixedTorus m) :
    ((reflection m .linear).val * (reflection m .suzuki).val)^4 * t.val *
      (((reflection m .linear).val * (reflection m .suzuki).val)^4)⁻¹ = t.val⁻¹ := by
  apply toSplitGroup_injective m
  simpa only [map_mul,map_inv,reflection,opposition] using opposition_splitTorus m t.property

/-- The literal product of torus actions has inversion as its fourth power. -/
theorem torusReflection_product_four (m : ℕ) (t : fixedTorus m) :
    ((torusReflection m .linear * torusReflection m .suzuki)^4) t = t⁻¹ := by
  rw [torusReflection,torusReflection,←map_mul,←map_pow]
  apply Subtype.ext
  exact reflection_product_four_inverts m t

end ReeF4.SmallCompletion
