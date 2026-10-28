module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeIntersection
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.HexacodeSection
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# The hexacode marking on the original M24-code section

The same selected pair and whole-code marking identify the literal intersection
B with the native even-code hyperplane. Recovery constructs coordinates on the
original B/U and intertwines its full relative-normalizer action with the native
hexacode quotient. Restricting to L_U retains the same map and gives exactly
O₂(L_U) as kernel, so the central cubic of 3.A6 remains in the action.

The private import exposes the existing component conjugation map only for
checking this action bridge, as in M24CodeNormalizer; no shared boundary changes.
Source: Aschbacher--Smith H.16.1(3) and 8.2.8(5), printed pp.402,718,
refs/quasithin.pdf. This supplies the actual marked B/U input for the later
tensor argument, on the original orbit and pair.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Atlas.Codes
open ChapterE Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open Chapter7.NormalizedSource
open Chapter8.Section02.HermitianSource Chapter8.Section02.MathieuShadowRows
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer
open MathieuCode.NormalizedShadowRows.CodeHexacode
open MathieuCode.SextetLayers.CoordinateTransport
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal original B/U carries the full native hexacode action. -/
theorem sourceOrbit_m24_code_hexacode_pair_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let N := L ⊓ normalizer (U : Set G)
      let R := localResidual L U
      let B := D.sourceOrbit ⊓ I.pCoreIn 2
      letI : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le
        (show B ≤ D.sourceOrbit from inf_le_left)
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      I ≤ centralizer (U : Set G) ∧
      rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      rank B = 10 ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* HexEvenAutomorphisms) ∧
      ∃ (c : M24) (f : N →* sextetStabilizer standardSextet)
        (r : R →* sextetStabilizer standardSextet),
        ((inducedAutomizer D.sourceOrbit A).map a.toMonoidHom).map
          (MulAut.conj c).toMonoidHom = SextetCore.core ∧
        (∀ w : D.sourceOrbit, (w : G) ∈ U ↔
          codeRepresentation c (E (Additive.ofMul w)) ∈ CodeFlags.sextetCodeSpace standardSextet) ∧
        (∀ w : D.sourceOrbit, (w : G) ∈ I.pCoreIn 2 ↔
          codeRepresentation c (E (Additive.ofMul w)) ∈ evenCode standardSextet) ∧
        Function.Surjective f ∧
        f.ker = (pCore 2 L).comap (inclusion (show N ≤ L from inf_le_left)) ∧
        (∀ l, (f l).val = c * a (D.mathieuComponentAutomizer ⟨l,l.property.1⟩) * c⁻¹) ∧
        ((sextetPartPerm standardSextet).comp f).ker = (centralizer (U : Set G)).subgroupOf N ∧
        r.range = solvableResidual (sextetStabilizer standardSextet) ∧ IsPGroup 2 r.ker ∧
        (pCore 2 R).map r = (nativeQuotient standardSextet).ker ∧
        (∀ x, r x = f (inclusion (localResidual_le L U) x)) ∧
        ∃ hNB : N ≤ normalizer (B : Set G),
          ∃ eB : Additive (B ⧸ U.subgroupOf B) ≃ₗ[ZMod 2] hexacode,
            (∀ n b, eB (sectionRepresentation N B U hNB inf_le_right n b) =
              hexAction (nativeQuotient standardSextet (f n)) (eB b)) ∧
            (sectionRepresentation N B U hNB inf_le_right).ker =
              (nativeQuotient standardSextet).ker.comap f ∧
            (∀ r₀ b, eB (sectionRepresentation R B U
                ((localResidual_le L U).trans hNB)
                ((localResidual_le L U).trans inf_le_right) r₀ b) =
              hexAction (nativeQuotient standardSextet (r r₀)) (eB b)) ∧
            (sectionRepresentation R B U
              ((localResidual_le L U).trans hNB)
              ((localResidual_le L U).trans inf_le_right)).ker = pCore 2 R ∧
            Module.finrank (ZMod 2) (Additive (B ⧸ U.subgroupOf B)) = 6 := by
  obtain ⟨I,i,S,s,hfix,hIC,hU,hTU,hB,hmodel,
    c,f,r,hc,hspace,hBspace,hf,hfk,hval,hpoint,hrange,hrker,hrcore,hrval⟩ :=
    D.sourceOrbit_m24_code_intersection_pair_of_many h hmany hV hq hnon a E hE hH
  let W := D.sourceOrbit
  let A := offenderNormalizer W i.val⁻¹
  let U := W ⊓ centralizer (A : Set G)
  let N := L ⊓ normalizer (U : Set G)
  let R := localResidual L U
  let B := W ⊓ I.pCoreIn 2
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le
    (show B ≤ W from inf_le_left)
  let F := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (codeRepresentation.asGroupHom c))
  have hNV : N ≤ normalizer (W : Set G) := inf_le_left.trans D.sourceOrbit_component_normalizes
  have hF (n : N) (v : W) :
      F (Additive.ofMul (W.normalizerMonoidHom (inclusion hNV n) v)) =
        codeRepresentation (f n).val (F (Additive.ofMul v)) := by
    change codeRepresentation c (E (automizerRepresentation W
      (D.mathieuComponentAutomizer ⟨n,n.property.1⟩) (Additive.ofMul v))) =
        codeRepresentation (f n).val (codeRepresentation c (E (Additive.ofMul v)))
    rw [hE,hval]
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  have hBF (v : W) : (v : G) ∈ B ↔ F (Additive.ofMul v) ∈ evenCode standardSextet := by
    exact ⟨fun hv => (hBspace v).mp hv.2,
      fun hv => ⟨v.property,(hBspace v).mpr hv⟩⟩
  obtain ⟨hNB,eB,heval,he⟩ := code_section_hexacode_coordinates W B U N inf_le_left
    hNV inf_le_right standardSextet f F hBF hspace hF
  have hk := code_section_hexacode_kernel B U N inf_le_right standardSextet f hNB eB he
  have hdim : Module.finrank (ZMod 2) (Additive (B ⧸ U.subgroupOf B)) = 6 :=
    eB.finrank_eq.trans hexacode_finrank
  have heR : ∀ r₀ b, eB (sectionRepresentation R B U
      ((localResidual_le L U).trans hNB)
      ((localResidual_le L U).trans inf_le_right) r₀ b) =
      hexAction (nativeQuotient standardSextet (r r₀)) (eB b) := by
    intro r₀ b
    rw [hrval]
    exact he (inclusion (localResidual_le L U) r₀) b
  have hkR : (sectionRepresentation R B U
      ((localResidual_le L U).trans hNB)
      ((localResidual_le L U).trans inf_le_right)).ker = pCore 2 R := by
    rw [code_section_hexacode_kernel B U R
      ((localResidual_le L U).trans inf_le_right) standardSextet r
      ((localResidual_le L U).trans hNB) eB heR, ←hrcore]
    exact Subgroup.comap_map_eq_self (le_sSup ⟨inferInstance,hrker⟩)
  refine ⟨I,i,S,s,hfix,hIC,hU,hTU,hB,hmodel,c,f,r,hc,hspace,hBspace,hf,hfk,hval,
    hpoint,hrange,hrker,hrcore,hrval,hNB,eB,he,hk,heR,hkR,hdim⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
