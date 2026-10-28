module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPointCentralizers
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryAutomizer

/-!
# Point quotients and odd indices on the original binary doubled orbit

The full marked automizer identifies the image of a nonidentity seed-point
centralizer with S₄. Its literal local centralizer maps onto S₄ with kernel
its intersection with C_G(W), where W is the original whole orbit. Every
odd subgroup consequently has index at most three over its centralizer of W.
The same estimate applies to every paired plane in the original coordinates,
retaining both the seed and its actual conjugate.

This proves the first clause of 7.7.4 without a numerical or centralizer
callback. Normalizer control of the odd kernel, the ambient containment
7.7.3, and the final binary exclusion remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, printed p.704, in `refs/quasithin.pdf`.
-/

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryLinearThree
public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal automizer of a nonidentity point of the original seed is S₄. Every odd local subgroup has image of order dividing three. -/
theorem sourceOrbit_binary_point_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (x : G) (hx : x ∈ V) (hx1 : x ≠ 1) :
    Nonempty (inducedAutomizer D.sourceOrbit (centralizer ({x} : Set G)) ≃*
      Equiv.Perm (Fin 4)) ∧
      ∀ Y : Subgroup G, Y ≤ normalizer (L : Set G) ⊓ centralizer ({x} : Set G) →
        Odd (Nat.card Y) → (centralizer (D.sourceOrbit : Set G)).relIndex Y ∣ 3 := by
  obtain ⟨_,_,_,q,hq,E,a,hE,ha,_,hcov,hV,_⟩ :=
    D.sourceOrbit_binary_automizer_model h hd F hF hmodel
  have hVW : V ≤ D.sourceOrbit := by
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  let w : Additive D.sourceOrbit := Additive.ofMul ⟨x,hVW hx⟩
  have hw2 : (E w).2 = 0 := (hV w).mpr hx
  have hv : (E w).1 ≠ 0 := by
    intro hz
    have hw : w = 0 := E.map_eq_zero_iff.mp (Prod.ext hz hw2)
    exact hx1 (congrArg (fun y : Additive D.sourceOrbit => (y.toMul : G)) hw)
  have hw : E.symm ((E w).1,0) = w := by
    apply E.injective
    rw [E.apply_symm_apply]
    exact Prod.ext rfl hw2.symm
  have hp := doubledBinary_point_fixer (automizerRepresentation D.sourceOrbit)
    (D.sourceOrbit.normalizerMonoidHom.rangeRestrict.comp
      (inclusion D.sourceOrbit_component_normalizes)) q hq E hE a ha hcov (E w).1 hv
  rw [hw] at hp
  constructor
  · change Nonempty (inducedAutomizer D.sourceOrbit
      (centralizer ({(w.toMul : G)} : Set G)) ≃* Equiv.Perm (Fin 4))
    rwa [doubledBinary_induced_point_fixer D.sourceOrbit w]
  · intro Y hY ho
    apply doubledBinary_odd_point_index D.sourceOrbit w hp Y _ ho
    rwa [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]

/-- The point version of source 7.7.4(1), with the intersection C_Y(W) explicit. -/
theorem sourceOrbit_binary_point_odd_index_le_three
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (x : G) (hx : x ∈ V) (hx1 : x ≠ 1)
    (Y : Subgroup G) (hY : Y ≤ normalizer (L : Set G) ⊓ centralizer ({x} : Set G))
    (hodd : Odd (Nat.card Y)) :
    (Y ⊓ centralizer (D.sourceOrbit : Set G)).relIndex Y ≤ 3 := by
  rw [inf_relIndex_left]
  exact Nat.le_of_dvd (by decide)
    ((D.sourceOrbit_binary_point_centralizer h hd F hF hmodel x hx hx1).2 Y hY hodd)

/-- The actual map from N_G(L) ∩ C_G(x) onto S₄, with its full kernel specified inside the original local subgroup. -/
theorem sourceOrbit_binary_point_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    (x : G) (hx : x ∈ V) (hx1 : x ≠ 1) :
    ∃ π : (normalizer (L : Set G) ⊓ centralizer ({x} : Set G) : Subgroup G) →*
        Equiv.Perm (Fin 4),
      Function.Surjective π ∧ π.ker = (centralizer (D.sourceOrbit : Set G)).subgroupOf
        (normalizer (L : Set G) ⊓ centralizer ({x} : Set G)) := by
  have hVW : V ≤ D.sourceOrbit := by
    rw [D.sourceOrbit_eq]
    exact le_componentOrbit V (T : Subgroup G)
  let w : Additive D.sourceOrbit := Additive.ofMul ⟨x,hVW hx⟩
  have he := (D.sourceOrbit_binary_point_centralizer h hd F hF hmodel x hx hx1).1
  change Nonempty (inducedAutomizer D.sourceOrbit
    (centralizer ({(w.toMul : G)} : Set G)) ≃* Equiv.Perm (Fin 4)) at he
  rw [doubledBinary_induced_point_fixer D.sourceOrbit w] at he
  have hh := doubledBinary_point_quotient D.sourceOrbit w he
  rwa [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd] at hh

open DoubledBinaryPlanes

/-- The paired-plane version of source 7.7.4(1), for the original conjugator and coordinate axes. -/
theorem sourceOrbit_binary_pairedPlane_odd_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∀ v : Vector, ∀ f : Module.Dual (ZMod 2) Vector, f v = 1 →
          ∀ Y : Subgroup G,
            Y ≤ normalizer (L : Set G) ⊓ centralizer (ambientPlane D.sourceOrbit E v f : Set G) →
            Odd (Nat.card Y) →
            (Y ⊓ centralizer (D.sourceOrbit : Set G)).relIndex Y ≤ 3 := by
  obtain ⟨t,ht,hnt,_,_,E,_,hV,hVt⟩ :=
    D.sourceOrbit_binary_pair_coordinates h hd F hF hmodel
  refine ⟨t,ht,hnt,E,hV,hVt,?_⟩
  intro v f hfv Y hY ho
  let w := E.symm (v,0)
  have hx : (w.toMul : G) ∈ V := (hV w).mp (by simp [w])
  have hx1 : (w.toMul : G) ≠ 1 := by
    intro he
    have hw : w = 0 := by
      apply Additive.toMul.injective
      exact Subtype.ext he
    have hv : v = 0 := by
      let p : Additive D.sourceOrbit →ₗ[ZMod 2] Vector :=
        (LinearMap.fst (ZMod 2) Vector (Module.Dual (ZMod 2) Vector)).comp E.toLinearMap
      have hz : p w = 0 := by rw [hw,map_zero]
      change (E w).1 = 0 at hz
      simpa only [w,E.apply_symm_apply] using hz
    simp [hv] at hfv
  apply D.sourceOrbit_binary_point_odd_index_le_three h hd F hF hmodel
    (w.toMul : G) hx hx1 Y _ ho
  apply hY.trans
  apply inf_le_inf_left
  apply centralizer_le
  intro x hx'
  obtain rfl := Set.mem_singleton_iff.mp hx'
  exact ((ambientPlane_le_iff D.sourceOrbit E v f
    (ambientPlane D.sourceOrbit E v f)).mp le_rfl).1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
