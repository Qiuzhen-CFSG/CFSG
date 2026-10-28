module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.Actions
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeRecovery
public import Theory.ElementaryAbelian.Quotient

/-!
# Hexacode coordinates on the original code quotient

The whole-code marking restricts to the literal subgroup B, whose image is
exactly the even-code hyperplane. Native recovery then has kernel U intersect
B, so its first-isomorphism equivalence identifies the actual quotient B/U
with the binary hexacode. Conjugation by the original actor descends through
this equivalence with the native sextet quotient, including its central cubic.
Faithfulness identifies the full section-action kernel with the preimage of
the native translations.

Source: Aschbacher--Smith H.16.1(3) and 8.2.8(5), printed pp.402,718,
refs/quasithin.pdf. The native recovery is the licensed ATLAS port cited in
Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeRecovery.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.SextetLayers.CoordinateTransport
open MathieuCode.NormalizedShadowRows.CodeHexacode
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows

private theorem evenCode_stable (S : Sextet) (g : sextetStabilizer S)
    (w : Code) (hw : w ∈ evenCode S) : codeRepresentation g.val w ∈ evenCode S := by
  obtain ⟨v,hv⟩ := evenProjection_surjective S ⟨w,hw⟩
  obtain ⟨s,rfl⟩ := (nativeStabilizerEquiv S).surjective g
  have he : codeRepresentation (nativeStabilizerEquiv S s).val w =
      (evenProjection S (sextetC0Action s v)).val := by
    have hv' : (evenProjection S v).val = w := congrArg Subtype.val hv
    rw [←hv']
    change codeRepresentation (nativeStabilizerEquiv S s).val
      (codeLine.mkQ (golayCoordinates S (C0.inclusion MathieuCode.NormalizedShadowRows.CodeHexacode.C0_le_golay v))) = _
    rw [codeRepresentation_mk,←golayCoordinates_equivariant]
    rfl
  rw [he]
  exact (evenProjection S (sextetC0Action s v)).property

variable {G : Type*} [Group G] (V B U K : Subgroup G) [IsElementaryAbelian 2 V]
  (hBV : B ≤ V) (hKV : K ≤ normalizer (V : Set G))
  (hKU : K ≤ normalizer (U : Set G))
  (S : Sextet) (f : K →* sextetStabilizer S)
  (F : Additive V ≃ₗ[ZMod 2] Code)
  (hB : ∀ v : V, (v : G) ∈ B ↔ F (Additive.ofMul v) ∈ evenCode S)
  (hU : ∀ v : V, (v : G) ∈ U ↔ F (Additive.ofMul v) ∈ CodeFlags.sextetCodeSpace S)
  (hF : ∀ k v, F (Additive.ofMul (V.normalizerMonoidHom (inclusion hKV k) v)) =
    codeRepresentation (f k).val (F (Additive.ofMul v)))

include hU hF in
theorem code_section_hexacode_coordinates :
    letI : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBV
    ∃ hKB : K ≤ normalizer (B : Set G),
      ∃ e : Additive (B ⧸ U.subgroupOf B) ≃ₗ[ZMod 2] hexacode,
        (∀ b : B, e (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf B) b)) =
          evenRecovery S ⟨F (Additive.ofMul (inclusion hBV b)),
            (hB (inclusion hBV b)).mp b.property⟩) ∧
        ∀ k v, e (sectionRepresentation K B U hKB hKU k v) =
          hexAction (nativeQuotient S (f k)) (e v) := by
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBV
  have hKB : K ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro k hk b hb
    let v : V := ⟨b,hBV hb⟩
    have hw := evenCode_stable S (f ⟨k,hk⟩) (F (Additive.ofMul v)) ((hB v).mp hb)
    rw [←hF] at hw
    exact (hB (V.normalizerMonoidHom (inclusion hKV ⟨k,hk⟩) v)).mpr hw
  let FB : Additive B →ₗ[ZMod 2] evenCode S :=
    (F.toLinearMap.comp ((inclusion hBV).toAdditive.toZModLinearMap 2)).codRestrict
      (evenCode S) (fun b => (hB (inclusion hBV b.toMul)).mp b.toMul.property)
  have hFB : Function.Surjective FB := by
    intro w
    obtain ⟨v,hv⟩ := F.surjective w.val
    have hb : (v.toMul : G) ∈ B := (hB v.toMul).mpr (hv ▸ w.property)
    refine ⟨Additive.ofMul ⟨v.toMul,hb⟩,?_⟩
    apply Subtype.ext
    exact hv
  let q : Additive B →ₗ[ZMod 2] hexacode := (evenRecovery S).comp FB
  let g : B →* Multiplicative hexacode := q.toAddMonoidHom.toMultiplicativeRight
  have hg : Function.Surjective g := (evenRecovery_surjective S).comp hFB
  have hk : g.ker = U.subgroupOf B := by
    ext b
    change evenRecovery S (FB (Additive.ofMul b)) = 0 ↔ (b : G) ∈ U
    rw [evenRecovery_kernel]
    exact (hU (inclusion hBV b)).symm
  let e0 : (B ⧸ U.subgroupOf B) ≃* Multiplicative hexacode :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  let e : Additive (B ⧸ U.subgroupOf B) ≃ₗ[ZMod 2] hexacode :=
    LinearEquiv.ofBijective (e0.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) e0.bijective
  have he (b : B) : e (Additive.ofMul (QuotientGroup.mk' (U.subgroupOf B) b)) =
      evenRecovery S (FB (Additive.ofMul b)) := by
    change e0 (QuotientGroup.mk' (U.subgroupOf B) b) = g b
    change QuotientGroup.quotientKerEquivOfSurjective g hg
      (QuotientGroup.quotientMulEquivOfEq hk.symm (QuotientGroup.mk' (U.subgroupOf B) b)) = _
    change QuotientGroup.quotientKerEquivOfSurjective g hg
      (QuotientGroup.quotientMulEquivOfEq hk.symm (b : B ⧸ U.subgroupOf B)) = _
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  refine ⟨hKB,e,he,?_⟩
  intro k v
  obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B) v.toMul
  have hv : v = Additive.ofMul (QuotientGroup.mk' (U.subgroupOf B) b) :=
    congrArg Additive.ofMul hb.symm
  rw [hv,sectionRepresentation_apply,he,he]
  have heq : FB (Additive.ofMul (B.normalizerMonoidHom (inclusion hKB k) b)) =
      (⟨codeRepresentation (f k).val (FB (Additive.ofMul b)).val,
        evenCode_stable S (f k) _ (FB (Additive.ofMul b)).property⟩ : evenCode S) := by
    apply Subtype.ext
    exact hF k (inclusion hBV b)
  rw [heq]
  exact evenRecovery_equivariant S (f k) (FB (Additive.ofMul b)) _

omit hBV hKV hB hU hF in
/-- The exact kernel on the original quotient is the preimage of native translations. -/
theorem code_section_hexacode_kernel
    [IsElementaryAbelian 2 B]
    (hKB : K ≤ normalizer (B : Set G))
    (e : Additive (B ⧸ U.subgroupOf B) ≃ₗ[ZMod 2] hexacode)
    (he : ∀ k v, e (sectionRepresentation K B U hKB hKU k v) =
      hexAction (nativeQuotient S (f k)) (e v)) :
    (sectionRepresentation K B U hKB hKU).ker = (nativeQuotient S).ker.comap f := by
  ext k
  change sectionRepresentation K B U hKB hKU k = 1 ↔ nativeQuotient S (f k) = 1
  constructor
  · intro hk
    apply hexAction_injective
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    have hh := he k v
    rw [hk] at hh
    change hexAction (nativeQuotient S (f k)) (e v) = e v
    simpa only [Module.End.one_apply] using hh.symm
  · intro hk
    apply LinearMap.ext
    intro v
    apply e.injective
    rw [he,hk,map_one]
    rfl

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
