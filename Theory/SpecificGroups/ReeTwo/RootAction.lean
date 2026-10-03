module

public import Theory.SpecificGroups.ReeTwo.Core
public import Mathlib.GroupTheory.OrderOfElement

/-!
# The specified complement action on the Ree two core

The root maps are the root-1 commutators and the Weyl table of Shinoda
(1975), pp. 81–83. We first verify the defining core relations for their
images. The presentation then makes them homomorphisms; checking their
powers on the ten generating roots makes them automorphisms.

Multiplication of automorphisms is composition, acting on the left. Thus
`a` describes right conjugation by root 1, and root 1 in a semidirect
product with this action must have complement coordinate `a⁻¹`.
-/

@[expose] public section
namespace ReeTwo
namespace Core

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Images under right conjugation by root 1. -/
def aRoot (i : CoreRoot) : Core := root i * (rootWord root (actionCorrection i))⁻¹

/-- Images under the Weyl involution. -/
def rRoot (i : CoreRoot) : Core := root (weylRoot i)

set_option maxRecDepth 8192 in
theorem aRoot_relations : CoreRelations aRoot where
  square := by decide +kernel
  commutator := by decide +kernel

set_option maxRecDepth 8192 in
theorem rRoot_relations : CoreRelations rRoot where
  square := by decide +kernel
  commutator := by decide +kernel

/-- Evaluate the root-1 action on the unique ordered normal form. -/
def aMap (g : Core) : Core := normalWord aRoot (coords g)

/-- Evaluate the Weyl action on the unique ordered normal form. -/
def rMap (g : Core) : Core := normalWord rRoot (coords g)

private theorem aMap_eq_lift (g : Core) : aMap g = lift aRoot_relations g :=
  (lift_apply aRoot_relations g).symm

private theorem rMap_eq_lift (g : Core) : rMap g = lift rRoot_relations g :=
  (lift_apply rRoot_relations g).symm

@[simp] theorem aMap_root (i : CoreRoot) : aMap (root i) = aRoot i := by
  rw [aMap_eq_lift, lift_root]

@[simp] theorem rMap_root (i : CoreRoot) : rMap (root i) = rRoot i := by
  rw [rMap_eq_lift, lift_root]

theorem aMap_four (g : Core) : aMap (aMap (aMap (aMap g))) = g := by
  have he : (lift aRoot_relations).comp ((lift aRoot_relations).comp
      ((lift aRoot_relations).comp (lift aRoot_relations))) = MonoidHom.id Core := by
    apply hom_ext
    intro i
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, ← aMap_eq_lift]
    exact (by decide +kernel : ∀ i : CoreRoot,
      aMap (aMap (aMap (aMap (root i)))) = root i) i
  simpa only [MonoidHom.comp_apply, MonoidHom.id_apply, ← aMap_eq_lift] using
    DFunLike.congr_fun he g

theorem rMap_two (g : Core) : rMap (rMap g) = g := by
  have he : (lift rRoot_relations).comp (lift rRoot_relations) = MonoidHom.id Core := by
    apply hom_ext
    intro i
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, ← rMap_eq_lift]
    exact (by decide +kernel : ∀ i : CoreRoot, rMap (rMap (root i)) = root i) i
  simpa only [MonoidHom.comp_apply, MonoidHom.id_apply, ← rMap_eq_lift] using
    DFunLike.congr_fun he g

/-- The specified right-conjugation automorphism of order four. -/
def a : MulAut Core where
  toFun := aMap
  invFun g := aMap (aMap (aMap g))
  left_inv := aMap_four
  right_inv := aMap_four
  map_mul' g h := by simpa only [aMap_eq_lift] using map_mul (lift aRoot_relations) g h

/-- The specified Weyl automorphism of order two. -/
def r : MulAut Core where
  toFun := rMap
  invFun := rMap
  left_inv := rMap_two
  right_inv := rMap_two
  map_mul' g h := by simpa only [rMap_eq_lift] using map_mul (lift rRoot_relations) g h

@[simp] theorem a_root (i : CoreRoot) :
    a (root i) = root i * (rootWord root (actionCorrection i))⁻¹ := aMap_root i

@[simp] theorem r_root (i : CoreRoot) : r (root i) = root (weylRoot i) := rMap_root i

/-- Equality of core automorphisms can be checked on the ten roots. -/
theorem aut_ext {f g : MulAut Core} (h : ∀ i, f (root i) = g (root i)) : f = g :=
  MulEquiv.toMonoidHom_injective (hom_ext h)

theorem a_four : a ^ 4 = 1 := by
  apply aut_ext
  exact (by decide +kernel : ∀ i : CoreRoot, (a ^ 4) (root i) = root i)

theorem r_two : r ^ 2 = 1 := by
  apply aut_ext
  exact (by decide +kernel : ∀ i : CoreRoot, (r ^ 2) (root i) = root i)

theorem orderOf_a : orderOf a = 4 := by
  have hne : a ^ 2 ≠ 1 := by
    intro h
    have he := congrArg (fun f : MulAut Core => f (root 0)) h
    exact (by decide +kernel : (a ^ 2) (root 0) ≠ root 0) he
  exact @orderOf_eq_prime_pow _ _ a 1 2 ⟨by decide +kernel⟩ hne a_four

theorem orderOf_r : orderOf r = 2 := by
  apply orderOf_eq_prime r_two
  intro h
  have he := congrArg (fun f : MulAut Core => f (root 0)) h
  exact (by decide +kernel : r (root 0) ≠ root 0) he

/-- The normal five-element generator, with composition acting on the left. -/
def c : MulAut Core := a ^ 2 * r

theorem c_five : c ^ 5 = 1 := by
  apply aut_ext
  exact (by decide +kernel : ∀ i : CoreRoot, (c ^ 5) (root i) = root i)

theorem orderOf_c : orderOf c = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide +kernel⟩
  apply orderOf_eq_prime c_five
  intro h
  have he := congrArg (fun f : MulAut Core => f (root 0)) h
  exact (by decide +kernel : c (root 0) ≠ root 0) he

set_option maxHeartbeats 8000000 in
theorem a_conj_c : a * c * a⁻¹ = c ^ 2 := by
  apply aut_ext
  exact (by decide +kernel : ∀ i : CoreRoot, (a * c * a⁻¹) (root i) = (c ^ 2) (root i))

end Core
end ReeTwo
