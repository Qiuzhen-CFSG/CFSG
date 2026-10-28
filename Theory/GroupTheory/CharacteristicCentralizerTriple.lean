module
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.GroupTheory.InvertingConjugates
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Trivial odd core from three conjugate involutions

A characteristic-two involution centralizer has trivial odd core. Its
intersection with an ambient normal odd subgroup is normal and odd, so the
involution acts without nonidentity fixed points and hence by inversion.
If three conjugates have central product, the ambient odd core is trivial.

The application in Aschbacher--Smith 13.2.12, printed pp.882--883, uses the
three singular vectors in the original binary A₅ module. This formulation
uses their exact product and avoids an additional hyperplane-generation step.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {D : Type*} [Group D] [Finite D]

/-- A characteristic-two involution centralizer forces inversion of the odd core. -/
theorem oddCore_inverted_of_characteristic_centralizer (z : D) (hz : z^2=1)
    (hc : centralizer (pCore 2 (centralizer ({z} : Set D)) : Set (centralizer ({z} : Set D))) ≤
      pCore 2 (centralizer ({z} : Set D))) :
    ∀ x ∈ pPrimeCore 2 D, MulAut.conj z x = x⁻¹ := by
  let C := centralizer ({z} : Set D)
  let O := pPrimeCore 2 D
  have hOc : O.subgroupOf C = ⊥ :=
    (pPrimeCore_eq_bot_iff.mp (pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hc))
      _ inferInstance (pPrimeCore_coprime_card.of_dvd_right
        (card_comap_dvd_of_injective O C.subtype C.subtype_injective))
  let a : MulAut O := MulAut.conjNormal z
  have hf : MonoidHom.FixedPointFree a := by
    intro x hx
    have he : z * (x : D) * z⁻¹ = (x : D) := congrArg Subtype.val hx
    have hxc : (x : D) ∈ C := mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he).symm
    have ho : (⟨x,hxc⟩ : C) ∈ O.subgroupOf C := x.property
    rw [hOc] at ho
    exact Subtype.ext (congrArg (fun y : C => (y : D)) (show (⟨x,hxc⟩ : C) = 1 from ho))
  have ha : Function.Involutive a := by
    intro x
    apply Subtype.ext
    change z * (z * (x : D) * z⁻¹) * z⁻¹ = (x : D)
    calc
      _ = (z*z) * (x : D) * (z*z)⁻¹ := by group
      _ = (x : D) := by rw [←pow_two,hz]; simp
  intro x hx
  exact congrArg Subtype.val (congrFun (hf.coe_eq_inv_of_involutive ha) (⟨x,hx⟩ : O))

/-- Three conjugate involutions with central product eliminate the odd core. -/
theorem oddCore_eq_bot_of_characteristic_centralizer_triple
    (z c d : D) (hz : z^2=1)
    (hc : centralizer (pCore 2 (centralizer ({z} : Set D)) :
      Set (centralizer ({z} : Set D))) ≤ pCore 2 (centralizer ({z} : Set D)))
    (hp : z * MulAut.conj c z * MulAut.conj d z ∈ center D) :
    pPrimeCore 2 D = ⊥ :=
  eq_bot_of_conjugate_inverters (pPrimeCore 2 D) pPrimeCore_coprime_card z c d
    (oddCore_inverted_of_characteristic_centralizer z hz hc)
    (mem_centralizer_iff.mpr fun x _ => mem_center_iff.mp hp x)

end Theory.GroupTheory
