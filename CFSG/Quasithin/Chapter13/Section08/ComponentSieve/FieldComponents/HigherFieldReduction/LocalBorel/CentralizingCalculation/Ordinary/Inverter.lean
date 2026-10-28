module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.NaturalImage
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.SourceData
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.OrdinaryInverter
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The marked inverter in the ordinary natural action

For the literal X = O²(N_LT(V₁)), the supplied Sylow subgroup of LT
restricts to L and maps onto a Sylow two-subgroup of its actual A₆ image.
The stable line makes this image normalize the residual image, which is
conjugate to the four-letter A₄. Its order is divisible by eight, so the
ordinary model calculation supplies an inverter. Lifting along the marked
Sylow image gives t in T ∩ L. The permutation kernel is a two-group,
so the image's two-core pulls back to O₂(X).

The constructed element is retained without taking a power. This proves
the inverter clause only; the Borel normalization and centralizer
displacement for that same element are supplied by the existing two-kernel
and centralizing-residual calculations.

Source: Aschbacher–Smith, 13.8.20, printed p.954/PDF p.971; the genuine
ordinary natural action is the setup preceding Notation 13.2.1, pp.876–877.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Inverter
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open BinaryPermutation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G] {L T V V₁ : Subgroup G}

private theorem image_conjugate (d : NaturalSetup L T V V₁) :
    ∃ g : S, (NaturalImage.onePermutation d).range.map (MulAut.conj g).toMonoidHom = K := by
  let M := parabolic L T V₁
  let f : M →* S := d.permutation.comp (inclusion inf_le_left)
  have he : (NaturalImage.onePermutation d).range = (pResidual 2 M).map f := by
    ext g
    constructor
    · rintro ⟨⟨x, y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y.val, y, hy, rfl⟩, rfl⟩
  have hm : (pResidual 2 M).map f = (pResidual 2 f.range).map f.range.subtype := by
    calc
      _ = ((pResidual 2 M).map f.rangeRestrict).map f.range.subtype := by rw [map_map]; rfl
      _ = _ := by rw [map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective]
  rw [he, hm]
  have hr : f.range = d.permutation.range ⊓
      subspaceStabilizer (naturalRepresentation (Fin 6)) d.point := d.line_normalizer_image
  rw [hr]
  exact OrdinaryNormalizer.point_residual_conjugate d.permutation.range d.alternating_le_range
    d.point d.point_dim

/-- The genuine ordinary source action supplies the marked inverter, retaining
the element of T ∩ L itself. -/
theorem exists_marked_inverter (d : NaturalSetup L T V V₁) :
    ∃ t : G, t ∈ T ∧ t ∈ L ∧ InvertsTwoCoreQuotient (one L T V₁) t := by
  let M := L ⊔ T
  let N := L.subgroupOf M
  let _ : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le L.le_normalizer d.normalizes_L)
  obtain ⟨P, hP⟩ := d.sylow.exists_subgroupOf_eq_of_normal N
  let e : N ≃* L := subgroupOfEquivOfLe (show L ≤ M from le_sup_left)
  let q : N →* alternatingGroup (Fin 6) :=
    d.model.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp e.toMonoidHom)
  have hq : Function.Surjective q :=
    d.model.surjective.comp ((QuotientGroup.mk'_surjective _).comp e.surjective)
  have hcompat (a : N) : d.permutation a.val = (q a).val := d.model_compatible (e a)
  let P' := P.mapSurjective hq
  let Q : Subgroup S := (P' : Subgroup (alternatingGroup (Fin 6))).map
    (alternatingGroup (Fin 6)).subtype
  have hQ : Q ≤ alternatingGroup (Fin 6) := map_subtype_le _
  have hcard : 8 ∣ Nat.card Q := by
    rw [card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective]
    apply P'.pow_dvd_card_of_pow_dvd_card (n := 3)
    rw [Theory.SpecificGroups.SymmetricSix.a6_order]
    decide
  have hmarked (a : N) (ha : a ∈ (P : Subgroup N)) : a.val.val ∈ T := by
    rw [hP, d.sylow_eq] at ha
    exact ha
  let X := one L T V₁
  let f := NaturalImage.onePermutation d
  let R := f.range
  have hnorm : Q ≤ normalizer (R : Set S) := by
    apply le_normalizer_iff.mpr
    rintro _ ⟨a', ha', rfl⟩ x ⟨y, rfl⟩
    obtain ⟨a, ha, rfl⟩ := ha'
    have ht := hmarked a ha
    have hn := T_normalizes_one L T V₁ d.line_stable ht
    have hy : a.val.val * y.val * a.val.val⁻¹ ∈ X :=
      le_normalizer_iff.mp (le_refl (normalizer (X : Set G))) _ hn _ y.property
    refine ⟨⟨a.val.val * y.val * a.val.val⁻¹, hy⟩, ?_⟩
    change d.permutation (a.val * inclusion ((one_le L T V₁).trans inf_le_left) y * a.val⁻¹) = _
    rw [map_mul, map_mul, map_inv, hcompat]
    rfl
  obtain ⟨u, hu, hinv⟩ := OrdinaryInverter.exists_inverter_of_conjugate R Q hQ hcard hnorm
    (image_conjugate d)
  obtain ⟨a', ha', rfl⟩ := hu
  obtain ⟨a, ha, rfl⟩ := ha'
  have ht := hmarked a ha
  have hn := T_normalizes_one L T V₁ d.line_stable ht
  refine ⟨a.val.val, ht, a.property, hn, ?_⟩
  intro x hx
  have hy : a.val.val * x * a.val.val⁻¹ * x ∈ X :=
    X.mul_mem (le_normalizer_iff.mp (le_refl (normalizer (X : Set G))) _ hn _ hx) hx
  let y : X := ⟨a.val.val * x * a.val.val⁻¹ * x, hy⟩
  have hm := hinv (f ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
  have he : f y = (q a).val * f ⟨x, hx⟩ * ((q a).val)⁻¹ * f ⟨x, hx⟩ := by
    change d.permutation (a.val * inclusion ((one_le L T V₁).trans inf_le_left) ⟨x, hx⟩ *
      a.val⁻¹ * inclusion ((one_le L T V₁).trans inf_le_left) ⟨x, hx⟩) = _
    rw [map_mul, map_mul, map_mul, map_inv, hcompat]
    rfl
  change (q a).val * f ⟨x, hx⟩ * ((q a).val)⁻¹ * f ⟨x, hx⟩ ∈ R.pCoreIn 2 at hm
  rw [← he] at hm
  have hk : IsPGroup 2 f.ker := by
    exact d.permutation_kernel_isPGroup.comap_of_injective
      (inclusion ((one_le L T V₁).trans inf_le_left))
      (inclusion_injective ((one_le L T V₁).trans inf_le_left))
  have hkr : IsPGroup 2 f.rangeRestrict.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hycore : y ∈ pCore 2 X := by
    rw [← f.rangeRestrict.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective hkr]
    change f.rangeRestrict y ∈ pCore 2 R
    obtain ⟨z, hz, hez⟩ := hm
    have hez' : z = f.rangeRestrict y := Subtype.ext hez
    exact hez' ▸ hz
  exact ⟨y, hycore, rfl⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Ordinary.Inverter
