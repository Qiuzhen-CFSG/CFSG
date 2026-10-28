module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPointControl
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPushingUpRemainder
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuRemaining

/-!
# Eliminate the original M23 branch and reduce M24 point pushing up

Each distinguished M23 cocode point centralizer contains an ambient Sylow
two-subgroup. Even characteristic and the actual C.2.8 configuration force
it into N_G(L). This discharges source 8.1.1 in the existing escaping-space
bound: r is at least seven and at most six. Thus the entire original M23
branch is excluded, without a pair-control or numerical hypothesis.

For M24 the same normal M22 residual excludes the contained-Fitting case.
The surviving ordinary component contains the original module and residual,
and its center contains the original distinguished involution. M24 point
containment, the M22 and M24 remaining module branches, and ambient J4
recognition remain with qt-d-1222-nonff-mathieu. The full M24 point quotient
Aut(M22), its residual M22, and the simple M22 outer markings are retained.

Source: Aschbacher--Smith, 8.1.1--3 and C.2.11--13,
printed pp.712--713 and148, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
open Sporadic.Mathieu MathieuCode Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuPairs
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- Source 8.1.1 on every original distinguished M23 cocode vector. -/
theorem sourceOrbit_m23_pair_control_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ (a : Automizer D.sourceOrbit ≃* M23)
      (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode),
      (∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
        m23CocodeRepresentation (a b) (E v)) ∧
      ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ m23WeightTwoOrbit →
        centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨a,E,hE,hc28⟩ := D.sourceOrbit_m23_hypothesisC28_of_many h hmany hV hq hnon
  refine ⟨a,E,hE,?_⟩
  intro x hx
  have hx1 : (x : G) ≠ 1 := by
    intro he
    apply m23WeightTwoOrbit_nonzero hx
    rw [show x = 1 from Subtype.ext he]
    exact E.map_zero
  have hpow : (x : G)^2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) x.property
  have hlocal := isTwoLocal_involution_centralizer (orderOf_eq_prime hpow hx1)
  obtain ⟨S,hSH⟩ := m23_pair_contains_sylow D.sourceOrbit T
    D.sourceOrbit_weakClosure_setup.normalizes a E hE x hx
  have hfit := generalizedFitting_eq_pCore_of_selfCentralizing 2
    (Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le S
      (h.simpleQTKE.evenCharacteristic S) hlocal hSH))
  obtain ⟨hc,⟨e⟩⟩ := hc28 x hx
  let H := centralizer ({(x : G)} : Set G)
  let M := normalizer (L : Set G)
  let C := L ⊓ H
  let B := (solvableResidual C).map C.subtype
  have hn : H ⊓ M ≤ normalizer (B : Set G) :=
    ((le_inf inf_le_right (inf_le_left.trans H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
  by_contra hout
  exact m22_seed_not_strict_of_characteristicTwo hc hn e hfit
    (lt_of_le_of_ne inf_le_left (fun he => hout (he.symm.le.trans inf_le_right)))

/-- The entire M23 branch is excluded on the original orbit: source 8.1.1
supplies the missing premise in r≥7, contradicting the proved r≤6. -/
theorem sourceOrbit_not_m23_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ¬ Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23) := by
  intro hq
  obtain ⟨a,E,hE,hpair⟩ := D.sourceOrbit_m23_pair_control_of_many h hmany hV hq hnon
  exact D.sourceOrbit_m23_false_of_pair_control h hmany hV hq hnon a E hE hpair

/-- An escaping M24 cocode point centralizer must have an actual ordinary
component containing the original residual and module. Its center contains
the same distinguished involution; the contained and constrained cases are excluded. -/
theorem sourceOrbit_m24_escaping_ordinary_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (x : D.sourceOrbit) (hx : E (Additive.ofMul x) ∈ weightTwoOrbit)
    (hout : ¬ centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G)) :
    let H := centralizer ({(x : G)} : Set G)
    let M := normalizer (L : Set G)
    let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ M).subgroupOf H ∧ B.subgroupOf H ≤ K ∧
      D.sourceOrbit.subgroupOf H ≤ K ∧
      ¬ D.sourceOrbit.subgroupOf H ≤ centralizer (K : Set H) ∧
      center K ≠ ⊥ ∧ (x : G) ∈ ((center K).map K.subtype).map H.subtype := by
  let H := centralizer ({(x : G)} : Set G)
  let M := normalizer (L : Set G)
  let C := L ⊓ H
  let B := (solvableResidual C).map C.subtype
  obtain ⟨hc,⟨e⟩,hf | ⟨K,hK,hnK,hKo,hBK,hxK⟩⟩ :=
    D.sourceOrbit_m24_pushingUp_remainder_of_many h hmany hV hq hnon a E hE x hx
  · have hn : H ⊓ M ≤ normalizer (B : Set G) :=
      ((le_inf inf_le_right (inf_le_left.trans H.le_normalizer)).trans
        inf_normalizer_le_normalizer_inf).trans
          (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
    exact (m22_seed_not_fitting_contained hc
      (lt_of_le_of_ne inf_le_left (fun he => hout (he.symm.le.trans inf_le_right))) hn e hf).elim
  · obtain ⟨hWK,hWn⟩ := hc.ordinary_module_placement K hK
    refine ⟨K,hK,hnK,hKo,hBK,hWK.trans inf_le_right,hWn,?_,hxK⟩
    intro hz
    have hx0 : (x : G) = 1 := by simpa only [hz,Subgroup.map_bot,mem_bot] using hxK
    apply weightTwoOrbit_nonzero hx
    rw [show x = 1 from Subtype.ext hx0]
    exact E.map_zero

/-- The original Mathieu branch has only the M22 and M24 simple quotients
left after the complete M12 and M23 exclusions. -/
theorem sourceOrbit_mathieu_m22_or_m24_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24) := by
  have hrem := D.sourceOrbit_mathieu_remaining_quotients_of_many h hmany hV hm hnon
  rcases hrem with h22 | h23 | h24
  · exact .inl h22
  · exact (D.sourceOrbit_not_m23_of_many h hmany hV hnon h23).elim
  · exact .inr h24

/-- Surviving literal module markings retain both simple M22 outer actions
and the full original M24 automizer, with all M23 alternatives removed. -/
theorem sourceOrbit_mathieu_m22_or_m24_markings_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    (Nonempty (ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source.MarkedSimpleModel
        D.orbitRepresentation D.orbitComponent m22OuterCodeRepresentation) ∨
      Nonempty (ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source.MarkedSimpleModel
        D.orbitRepresentation D.orbitComponent m22OuterCocodeRepresentation)) ∨
      Representation.MathieuSmall.IsM24ToddOrDual
        (automizerRepresentation D.sourceOrbit) := by
  rcases D.sourceOrbit_mathieu_m22_or_m24_of_many h hmany hV hm hnon with h22 | h24
  · exact .inl (D.sourceOrbit_m22_simple_marking_of_many h hmany hV h22 hnon)
  · exact .inr (D.sourceOrbit_m24_automizer_marking h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) h24)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
