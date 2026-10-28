module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentGeometry
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryOddCore

/-!
# Singular component-centralizing points on the original doubled orbit

A subgroup whose fixed space on W properly contains a paired plane centralizes
a singular point outside both original seed axes. The literal component action
places this point in the centralizer of a Sylow two-subgroup of G, so source
even characteristic makes its ambient centralizer characteristic two.

This supplies the geometric point used in the component paragraph of 7.7.6.
It does not yet assert characteristic two for the intersection with the escaping
H (7.7.5), or eliminate the components of H. Those remaining steps and the final
non-FF assembly belong to qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, H.4.2 and 7.7.6, printed pp.380 and 706,
refs/quasithin.pdf.
-/

open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryComponentGeometry
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- A larger component-fixed space supplies a singular involution with an ambient
characteristic-two centralizer, retaining the original seed and its conjugate. -/
theorem sourceOrbit_binary_pairedPlane_component_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∀ (v : Vector) (f : Module.Dual (ZMod 2) Vector), f v = 1 →
          ∀ K : Subgroup G,
            ambientPlane D.sourceOrbit E v f < D.sourceOrbit ⊓ centralizer (K : Set G) →
            ∃ w : Additive D.sourceOrbit,
              (w.toMul : G) ∈ centralizer (K : Set G) ∧
              (w.toMul : G) ∉ V ∧
              (w.toMul : G) ∉ V.map (MulAut.conj t).toMonoidHom ∧
              IsSingular (E w) ∧ orderOf (w.toMul : G) = 2 ∧
              (∃ S : Sylow 2 G,
                (S : Subgroup G) ≤ centralizer ({(w.toMul : G)} : Set G)) ∧
              centralizer ({(w.toMul : G)} : Set G) ∈ Chapter1.He G := by
  obtain ⟨t,ht,hnt,q,hq,E,a,hE,_,_,hcov,hV,hVt⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,?_⟩
  intro v f hfv K hK
  obtain ⟨w,hwK,hwv,hwf,hwp⟩ := ambientPlane_lt_singular D.sourceOrbit E v f hfv
    (centralizer (K : Set G)) hK
  have hws : IsSingular (E w) := ⟨hwv,hwf,hwp⟩
  obtain ⟨S,hS⟩ := ambient_singular_sylow D.sourceOrbit L T
    D.sourceOrbit_weakClosure_setup.normalizes D.sourceOrbit_component_normalizes
    q hq E hE a hcov w hws
  have hw1 : (w.toMul : G) ≠ 1 := by
    intro he
    have hz : w = 0 := Additive.toMul.injective (Subtype.ext he)
    exact hwv (by rw [hz,map_zero]; rfl)
  have ho : orderOf (w.toMul : G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (w.toMul : G) w.toMul.property) hw1
  have hp : IsPGroup 2 (zpowers (w.toMul : G)) :=
    (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le (zpowers_le.mpr w.toMul.property)
  have hz : zpowers (w.toMul : G) ≠ ⊥ := by
    intro he
    exact hw1 (mem_bot.mp (he ▸ mem_zpowers (w.toMul : G)))
  have hchar : centralizer ({(w.toMul : G)} : Set G) ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le S (h.simpleQTKE.evenCharacteristic S)
      ⟨zpowers (w.toMul : G),hz,hp,
        (normalizer_zpowers_eq_centralizer_of_order_two (w.toMul : G) ho).symm⟩ hS
  exact ⟨w,hwK,fun hv => hwf ((hV w).mpr hv),
    fun hv => hwv ((hVt w).mpr hv),hws,ho,⟨S,hS⟩,hchar⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
