module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.AmbientActions.GeneratorAgreement
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group
/-!
# Literal words for a Fi24 involution-centralizer section

The involution is the first retained ATLAS generator. Two short Bray words
centralize it as soon as the corresponding fifth-power relations are checked.
The two final lifting words were discovered in their action on a 3510-point
orbit; subsequent certificates compare that action with the literal Fi22
source generators. No identification of the whole centralizer is needed.
Source: GLS3 Table5.3i Fischer paragraph and Aschbacher--Smith A.2.19.
-/
@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.CentralizerSection
open Subgroup
open Fi23Lift.Certificate.Ambient

def a : Carrier := ⟨generatorA, subset_closure (by simp)⟩
def b : Carrier := ⟨generatorB, subset_closure (by simp)⟩

theorem a_inv : a⁻¹ = a := by
  have H : generatorA⁻¹ = generatorA := by
    apply Equiv.ext
    intro i
    calc
      generatorA⁻¹ i = aInvMap i := (aInvMap_correct i).symm
      _ = aMap i := rfl
      _ = generatorA i := aMap_correct i
  exact Subtype.ext H

theorem a_mul_self : a*a=1 := by
  simpa only [a_inv] using inv_mul_cancel a

theorem a_ne_one : a ≠ 1 := by
  intro h
  have H := congrArg (fun x : Carrier => inclusion x) h
  rw [map_one] at H
  have ha : inclusion a = generatorA := rfl
  rw [ha] at H
  have H0 : generatorA 0 = 0 := Equiv.congr_fun H 0
  exact (by decide +kernel : aMap 0 ≠ 0) ((aMap_correct 0).trans H0)

theorem a_order : orderOf a=2 :=
  orderOf_eq_prime (by simpa only [pow_two] using a_mul_self) a_ne_one

def g0 : Carrier := a*b*a*b^2*a*b^2*a*b
def g1 : Carrier := a*b^2*a*b*a*b^2
def k0 : Carrier := a*(g0⁻¹*a*g0)
def k1 : Carrier := a*(g1⁻¹*a*g1)
def h0 : Carrier := g0*k0^2
def h1 : Carrier := g1*k1^2

private lemma bray_five {G : Type*} [Group G] (a g : G) (ha : a * a = 1)
    (h5 : (a * (g⁻¹ * a * g)) ^ 5 = 1) :
    Commute a (g * (a * (g⁻¹ * a * g)) ^ 2) := by
  let b := g⁻¹ * a * g
  let c := a * b
  have hb : b * b = 1 := by
    calc
      b * b = g⁻¹ * (a * a) * g := by dsimp [b]; group
      _ = 1 := by rw [ha]; simp
  have hc : c * a * c = a := by
    calc
      c * a * c = a * ((b * (a * a)) * b) := by dsimp [c]; group
      _ = a := by rw [ha, mul_one, hb, mul_one]
  have hc2 : c ^ 2 * a * c ^ 2 = a := by
    calc
      c ^ 2 * a * c ^ 2 = c * (c * a * c) * c := by simp only [pow_two, mul_assoc]
      _ = a := by rw [hc, hc]
  have hc5 : c ^ 2 * c ^ 3 = 1 := by
    rw [← pow_add]
    exact h5
  have hm : c ^ 2 * a = a * c ^ 3 := by
    calc
      c ^ 2 * a = (c ^ 2 * a) * (c ^ 2 * c ^ 3) := by rw [hc5, mul_one]
      _ = (c ^ 2 * a * c ^ 2) * c ^ 3 := by group
      _ = a * c ^ 3 := by rw [hc2]
  have hag : a * g = g * b := by dsimp [b]; group
  have hba : b = a * c := by
    dsimp [c]
    rw [← mul_assoc, ha, one_mul]
  change a * (g * c ^ 2) = (g * c ^ 2) * a
  calc
    a * (g * c ^ 2) = (a * g) * c ^ 2 := by group
    _ = (g * b) * c ^ 2 := by rw [hag]
    _ = g * (a * c ^ 3) := by rw [hba]; group
    _ = (g * c ^ 2) * a := by rw [← hm]; group

theorem h0_commute (h : k0^5=1) : Commute a h0 :=
  bray_five a g0 a_mul_self h

theorem h1_commute (h : k1^5=1) : Commute a h1 :=
  bray_five a g1 a_mul_self h

def liftBaseA : Carrier := (h0)^3 * h1 * (h0)^2 * h1 * h0 * h1 * h0⁻¹ * (h1)^2
def liftA : Carrier := liftBaseA^15
def liftB : Carrier := h0 * h1 * h0 * h1 * (h0)^3 * h1⁻¹ * (h0)^3 * h1⁻¹ * h0 * h1 * h0 * h1 * (h0)^2 * h1 * h0⁻¹ * h1 * h0⁻¹ * h1 * (h0⁻¹)^3 * h1 * (h0⁻¹)^3 * h1⁻¹ * h0⁻¹ * h1⁻¹ * h0⁻¹

theorem liftA_centralizes (h0c : Commute a h0) (h1c : Commute a h1) :
    liftA ∈ centralizer ({a} : Set Carrier) := by
  have hh0 : h0 ∈ centralizer ({a} : Set Carrier) := mem_centralizer_singleton_iff.mpr h0c.eq.symm
  have hh1 : h1 ∈ centralizer ({a} : Set Carrier) := mem_centralizer_singleton_iff.mpr h1c.eq.symm
  unfold liftA liftBaseA
  exact pow_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (pow_mem hh0 3) hh1) (pow_mem hh0 2)) hh1) hh0) hh1) (inv_mem hh0)) (pow_mem hh1 2)) 15

theorem liftB_centralizes (h0c : Commute a h0) (h1c : Commute a h1) :
    liftB ∈ centralizer ({a} : Set Carrier) := by
  have hh0 : h0 ∈ centralizer ({a} : Set Carrier) := mem_centralizer_singleton_iff.mpr h0c.eq.symm
  have hh1 : h1 ∈ centralizer ({a} : Set Carrier) := mem_centralizer_singleton_iff.mpr h1c.eq.symm
  unfold liftB
  exact (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hh0 hh1) hh0) hh1) (pow_mem hh0 3)) (inv_mem hh1)) (pow_mem hh0 3)) (inv_mem hh1)) hh0) hh1) hh0) hh1) (pow_mem hh0 2)) hh1) (inv_mem hh0)) hh1) (inv_mem hh0)) hh1) (pow_mem (inv_mem hh0) 3)) hh1) (pow_mem (inv_mem hh0) 3)) (inv_mem hh1)) (inv_mem hh0)) (inv_mem hh1)) (inv_mem hh0))
end Sporadic.Fischer.Fi24Prime.CentralizerSection
