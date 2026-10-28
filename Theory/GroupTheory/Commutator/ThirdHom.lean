module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Hom.Instances

/-!
# The central third commutator as a homomorphism in each variable

If [G′,G] lies in the center, the literal third commutator [[x,y],z]
defines a nested homomorphism from three copies of G to its center.
No finiteness, exponent or coordinate assumption is required.

First, the central commutator pairing G′ × G → Z(G) is multiplicative
in both variables. Conjugation changes an element of G′ by an element
of the center, which the pairing kills. Applying the two commutator
product identities then proves multiplicativity in the first two inputs.
This is the group-theoretic input for descending the nonzero third
commutator of a class-three group to a trilinear form on its abelianization.

Source: standard class-three commutator calculus, using Mathlib's two
commutator product identities. Its current consumer is the exclusion of
order15 automorphisms on the binary four-dimensional Frattini quotient.
-/

namespace Subgroup
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G]

private theorem basic_comm_mem (x y : G) : ⁅x,y⁆ ∈ _root_.commutator G :=
  commutator_mem_commutator (mem_top x) (mem_top y)

private def centralDerivedPairing
    (hc : ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ ≤ center G) :
    _root_.commutator G →* (G →* center G) where
  toFun d := {
    toFun := fun x => ⟨⁅(d : G), x⁆, hc (commutator_mem_commutator d.property (mem_top x))⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro x y
      apply Subtype.ext
      change ⁅(d : G), x*y⁆ = ⁅(d : G), x⁆ * ⁅(d : G), y⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have hz := hc (commutator_mem_commutator d.property (mem_top y))
      have h := mem_center_iff.mp hz x
      calc
        ⁅(d:G),x⁆ * x * ⁅(d:G),y⁆ * x⁻¹ =
            ⁅(d:G),x⁆ * (x * ⁅(d:G),y⁆ * x⁻¹) := by simp only [mul_assoc]
        _ = _ := by rw [h, mul_inv_cancel_right] }
  map_one' := by ext x; simp
  map_mul' := by
    intro d e
    ext x
    change ⁅(d : G)*(e : G), x⁆ = ⁅(d : G), x⁆ * ⁅(e : G), x⁆
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hz := hc (commutator_mem_commutator e.property (mem_top x))
    have h := mem_center_iff.mp hz d
    rw [h, mul_inv_cancel_right]
    exact (mem_center_iff.mp hz ⁅(d : G),x⁆).symm

private theorem centralDerivedPairing_conj
    (hc : ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ ≤ center G)
    (g : G) (d : _root_.commutator G) :
    centralDerivedPairing hc
      ⟨g * d * g⁻¹, (inferInstance : (_root_.commutator G).Normal).conj_mem d d.property g⟩ =
      centralDerivedPairing hc d := by
  ext x
  have hcomm : ⁅g, (d : G)⁆ ∈ center G := by
    have h : ⁅(⊤ : Subgroup G), _root_.commutator G⁆ ≤ center G := by
      simpa only [commutator_comm (⊤ : Subgroup G)] using hc
    exact h (commutator_mem_commutator (mem_top g) d.property)
  change ⁅g*(d:G)*g⁻¹,x⁆ = ⁅(d:G),x⁆
  have heq : g*(d:G)*g⁻¹ = ⁅g,(d:G)⁆ * (d:G) := by
    simp only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
  rw [heq, commutatorElement_mul_left_eq_conj_mul]
  have hz : ⁅⁅g,(d:G)⁆,x⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_center_iff.mp hcomm x).symm
  rw [hz, mul_one, ← (mem_center_iff.mp hcomm ⁅(d:G),x⁆), mul_inv_cancel_right]

/-- The actual central third commutator is multiplicative in each of its inputs. -/
public theorem exists_third_commutator_hom
    (hc : ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ ≤ center G) :
    ∃ f : G →* (G →* (G →* center G)),
      ∀ x y z : G, ((f x y z : center G) : G) = ⁅⁅x,y⁆,z⁆ := by
  let c := centralDerivedPairing hc
  have hinv (g : G) (d : _root_.commutator G) :
      c ⟨g*d*g⁻¹, (inferInstance : (_root_.commutator G).Normal).conj_mem d d.property g⟩ = c d :=
    centralDerivedPairing_conj hc g d
  let f : G →* (G →* (G →* center G)) := {
    toFun := fun x => {
      toFun := fun y => c ⟨⁅x,y⁆, basic_comm_mem x y⟩
      map_one' := by
        change c ⟨⁅x,1⁆,_⟩ = 1
        rw [show (⟨⁅x,1⁆, _⟩ : _root_.commutator G) = 1 from Subtype.ext (by simp), map_one]
      map_mul' := by
        intro y z
        have heq : (⟨⁅x,y*z⁆, basic_comm_mem x (y*z)⟩ : _root_.commutator G) =
            ⟨⁅x,y⁆, basic_comm_mem x y⟩ *
              ⟨y * ⁅x,z⁆ * y⁻¹, (inferInstance : (_root_.commutator G).Normal).conj_mem _
                (basic_comm_mem x z) y⟩ := by
          apply Subtype.ext
          simpa only [Subgroup.coe_mul, mul_assoc] using commutatorElement_mul_right_eq_mul_conj x y z
        rw [heq, map_mul, hinv y ⟨⁅x,z⁆, basic_comm_mem x z⟩] }
    map_one' := by
      ext y z
      change (c ⟨⁅1,y⁆,_⟩ z : G) = 1
      simp [c, centralDerivedPairing]
    map_mul' := by
      intro x y
      ext z w
      have heq : (⟨⁅x*y,z⁆, basic_comm_mem (x*y) z⟩ : _root_.commutator G) =
          ⟨x * ⁅y,z⁆ * x⁻¹, (inferInstance : (_root_.commutator G).Normal).conj_mem _
            (basic_comm_mem y z) x⟩ *
            ⟨⁅x,z⁆, basic_comm_mem x z⟩ := by
        apply Subtype.ext
        exact commutatorElement_mul_left_eq_conj_mul x y z
      change (c ⟨⁅x*y,z⁆,_⟩ w : G) =
        (c ⟨⁅x,z⁆,_⟩ w : G) * (c ⟨⁅y,z⁆,_⟩ w : G)
      rw [heq, map_mul, hinv x ⟨⁅y,z⁆, basic_comm_mem y z⟩]
      exact congrArg Subtype.val (mul_comm _ _) }
  exact ⟨f, fun _ _ _ => rfl⟩

end Subgroup
