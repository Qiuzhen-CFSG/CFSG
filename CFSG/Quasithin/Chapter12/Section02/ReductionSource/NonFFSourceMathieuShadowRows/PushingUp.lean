module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.PointAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPushingUp
-- Intentional internal continuation: reuse the original C.2.8 constructor,
-- supplying its full section-centralizer and two-core premises for the M22 row.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPushingUp

/-!
# Original M22 cocode pushing-up configuration

The original point residual is a normal C-component, with projective model
PSL₃(4), and moves the entire original cocode. Its full local point action
controls the two-core and the section centralizer. The original centralizer
Sylow and characteristic-normalizer control therefore supply every clause
of C.2.8, without deleting the central covering kernel.

This is the setup in Aschbacher--Smith 8.1.1, p.712. The subsequent C.4.8
exclusion, hence distinguished-point containment, is a separate next step.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode Chapter7.NormalizedSource.MathieuPairs
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The point centralizer has exactly the original O₂(LT), with no
assumption that the original covering kernel is a two-group. -/
theorem sourceOrbit_m22_cocode_point_core
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hV : V = D.sourceOrbit)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation)
    (x : D.sourceOrbit) (i : Fin 22)
    (hx : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul x) = m22WeightTwoVector i) :
    ((L ⊔ (T : Subgroup G)) ⊓ centralizer ({(x : G)} : Set G)).pCoreIn 2 =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let H := centralizer ({(x : G)} : Set G)
  have hJN : J ≤ normalizer (D.sourceOrbit : Set G) :=
    sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes
  obtain ⟨f,hker,himage⟩ := D.sourceOrbit_m22_cocode_point_action h d x i hx
    (J ⊓ H) (inf_le_left.trans hJN) inf_le_right (inf_le_inf_right H le_sup_left)
  exact Chapter8.MathieuShadowRows.m22_point_core_eq D.sourceOrbit J hJN
    (hV ▸ D.core_centralizes) x f (himage ▸ map_le_range f _) hker

/-- Every original distinguished cocode vector supplies all of C.2.8 and
the actual residual's full projective PSL₃(4) marking. -/
theorem sourceOrbit_m22_cocode_hypothesisC28_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation)
    (x : D.sourceOrbit) (i : Fin 22)
    (hx : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul x) = m22WeightTwoVector i) :
    let H := centralizer ({(x : G)} : Set G)
    let A := H ⊓ normalizer (L : Set G)
    let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H A B
      ((L ⊔ (T : Subgroup G)).pCoreIn 2) D.sourceOrbit ∧
      IsQuasisimple (B ⧸ pCore 2 B) ∧
      Nonempty (((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* Matrix.PSL3Four.PSL) := by
  let H := centralizer ({(x : G)} : Set G)
  let A := H ⊓ normalizer (L : Set G)
  let C := L ⊓ H
  let B := (solvableResidual C).map C.subtype
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hCA : C ≤ A := le_inf inf_le_right (inf_le_left.trans L.le_normalizer)
  have hBA : B ≤ A := (map_subtype_le _).trans hCA
  obtain ⟨hn,hc,hq,he,hspan⟩ := D.sourceOrbit_m22_cocode_point_component h.toHypothesis1221 d x i hx
  obtain ⟨_,_,_,_,hm⟩ := D.sourceOrbit_m22_cocode_point_residual d x i hx
  have hAB : A ≤ normalizer (B : Set G) := (normal_subgroupOf_iff_le_normalizer hBA).mp hn
  have hWB : D.sourceOrbit ≤ B := by
    have hWA : D.sourceOrbit ≤ A := le_inf
      ((le_centralizer D.sourceOrbit).trans
        (centralizer_le (Set.singleton_subset_iff.mpr x.property)))
      (D.sourceOrbit_weakClosure_setup.le_sylow.trans D.sylow_normalizes_component)
    rw [←hm]
    exact le_normalizer_iff_commutator_le_right.mp (hWA.trans hAB)
  have hcore : (B ⊔ Q).pCoreIn 2 = Q := by
    have hK := D.sourceOrbit_m22_cocode_point_core h.toHypothesis1221 hV d x i hx
    have hBK : B ≤ (L ⊔ (T : Subgroup G)) ⊓ H :=
      (map_subtype_le _).trans (inf_le_inf_right H le_sup_left)
    have hKA : (L ⊔ (T : Subgroup G)) ⊓ H ≤ A :=
      le_inf inf_le_right (inf_le_left.trans
        (sup_le L.le_normalizer D.sylow_normalizes_component))
    have hh := normal_core_join B ((L ⊔ (T : Subgroup G)) ⊓ H) hBK (hKA.trans hAB)
    rwa [hK] at hh
  have hx1 : x ≠ 1 := by
    intro he
    apply m22WeightTwoVector_ne_zero i
    rw [←hx,he]
    exact LinearEquiv.map_zero _
  exact ⟨D.point_C28 h hV x hx1 B hBA hn hc hspan hWB hm hcore
    (D.sourceOrbit_m22_cocode_point_section_of_many h hmany hV hnon d x i hx),hq,he⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
