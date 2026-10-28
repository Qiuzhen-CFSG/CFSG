module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeNormalizer
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.Intersection
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Elementary

/-!
# The ten-dimensional intersection for the original M24-code pair

The original V has dimension eleven and its image in I/O₂(I) has rank one.
Thus B = V intersect O₂(I) has dimension ten. Its offender commutators fill
the native even-code hyperplane, giving the coordinates on the same B and
retaining the same fixed four-space U, conjugated marking, relative normalizer
and residual action with its genuine cubic kernel.

Source: Aschbacher--Smith 8.2.2(7), 8.2.5--6 and 8.2.8(5), printed
pp.715--718, refs/quasithin.pdf. This identifies the source section before
hexacode recovery or the later tensor argument is applied.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open ChapterE Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open Chapter7.NormalizedSource
open Chapter8.Section02.HermitianSource Chapter8.Section02.MathieuShadowRows
open Chapter8.Section02.Offenders Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Offenders.Parabolic
open Chapter8.Section02.Normalizer
open MathieuCode.NormalizedShadowRows.CodeHexacode
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original B has precisely the native even-code coordinates. -/
theorem sourceOrbit_m24_code_intersection_pair_of_many
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
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      I ≤ centralizer (U : Set G) ∧
      rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      rank (D.sourceOrbit ⊓ I.pCoreIn 2 : Subgroup G) = 10 ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
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
        (pCore 2 R).map r = (SextetLayers.CoordinateTransport.nativeQuotient standardSextet).ker ∧
        ∀ x, r x = f (inclusion (localResidual_le L U) x) := by
  obtain ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hU,hUT,hTU,hlocal,hchar,hcomp,hmodel,
    c,f,r,hc,hspace,hf,hfk,hval,hpoint,hrange,hrker,hrcore,hrval⟩ :=
    D.sourceOrbit_m24_code_normalizer_pair_of_many h hmany hV hq hnon a E hE hH
  let W := D.sourceOrbit
  let A := offenderNormalizer W i.val⁻¹
  let U := W ⊓ centralizer (A : Set G)
  let P := I.pCoreIn 2
  let B := W ⊓ P
  have hVI : W ≤ I := s.generate ▸ le_sup_left
  have hVN : W ≤ normalizer (P : Set G) := hVI.trans
    (I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I)))
  have hA := (selected_offender_of_parameter_bound s D.sourceOrbit_weakClosure_setup
    (by rw [hw]; rfl)).2.2.1
  change A = W.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ P at hA
  have hAP : A ≤ P := hA ▸ inf_le_right
  have hcor : subgroupCorank W B = 1 :=
    (quotient_rank_eq_core_corank I W hVI).symm.trans s.rank_eq
  have hsum := offender_corank_add (W := W) (A := B) (B := ⊥) bot_le inf_le_left
  have hv : rank W = 11 :=
    (Chapter7.log_card_eq_finrank W).trans (E.finrank_eq.trans finrank_code)
  have hrank : rank B = 10 := by
    have hsum' : rank W = subgroupCorank W B + rank B := by
      simpa only [subgroupCorank,relIndex_bot_left,rank] using hsum
    omega
  let F := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (codeRepresentation.asGroupHom c))
  let p : Automizer W →* M24 := (MulAut.conj c).toMonoidHom.comp a.toMonoidHom
  have hF (b : Automizer W) (v : Additive W) :
      F (automizerRepresentation W b v) = codeRepresentation (p b) (F v) := by
    change codeRepresentation c (E (automizerRepresentation W b v)) =
      codeRepresentation (c * a b * c⁻¹) (codeRepresentation c (E v))
    rw [hE]
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  have hcp : (inducedAutomizer W A).map p = CodeFlags.sextetCore standardSextet := by
    change (inducedAutomizer W A).map ((MulAut.conj c).toMonoidHom.comp a.toMonoidHom) = _
    rw [←Subgroup.map_map]
    exact hc
  have hBspace := code_intersection_coordinates W P A hVN hAP
    standardSextet p F hF hcp hrank
  exact ⟨I,i,S,s,hfix,hIC,hU,hTU,hrank,hmodel,c,f,r,hc,hspace,hBspace,
    hf,hfk,hval,hpoint,hrange,hrker,hrcore,hrval⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
