module
public import Theory.GroupTheory.PCoreFrattiniDisplacement
public import Theory.Frattini.BinarySquares
public import Theory.ElementaryAbelian.Basic

/-!
# Quadratic actors disjoint from a self-centralizing two-core

If an actor is quadratic on a self-centralizing two-core, the commutator
of an actor square with the core is a square in the core. It therefore
vanishes on the Frattini quotient. Burnside's exact Frattini action kernel
puts every actor square in the core. A disjoint actor consequently has
exponent two and is elementary abelian.

This is the group-level quadratic-actor step used in DGS85, Groups and
Graphs (1985), (5.8)--(5.9) and the proof of (11.6), pp.109--110,173.
No abelianness of the core or faithfulness on an assumed module is needed.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {H : Type*} [Group H] [Finite H]

/-- A quadratic actor square lies in the actual self-centralizing two-core. -/
theorem square_mem_pCore_of_quadratic
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (A : Subgroup H) (hq : ⁅⁅A,pCore 2 H⁆,A⁆ = ⊥)
    (a : H) (ha : a ∈ A) : a ^ 2 ∈ pCore 2 H := by
  apply mem_pCore_of_frattini_displacement hc
  intro x
  have hx : ⁅a,(x : H)⁆ ∈ pCore 2 H :=
    commutator_le_right A (pCore 2 H) (commutator_mem_commutator ha x.property)
  have hfix : a * ⁅a,(x : H)⁆ * a⁻¹ = ⁅a,(x : H)⁆ := by
    have hh := (commutator_eq_bot_iff_le_centralizer.mp hq)
      (commutator_mem_commutator ha x.property) a ha
    rw [hh,mul_inv_cancel_right]
  have he : ⁅a^2,(x : H)⁆ = ⁅a,(x : H)⁆^2 := by
    rw [pow_two,commutatorElement_mul_left_eq_conj_mul,hfix,←pow_two]
  rw [he]
  refine ⟨(⟨⁅a,(x : H)⁆,hx⟩ : pCore 2 H)^2, ?_, rfl⟩
  rw [(pCore_isPGroup (p := 2) (G := H)).frattini_eq_closure_squares]
  exact subset_closure ⟨_,rfl⟩

/-- A quadratic actor disjoint from a self-centralizing two-core is elementary. -/
theorem isElementaryAbelian_of_disjoint_pCore_quadratic
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (A : Subgroup H) (hq : ⁅⁅A,pCore 2 H⁆,A⁆ = ⊥)
    (hd : Disjoint A (pCore 2 H)) : IsElementaryAbelian 2 A := by
  have hs (a : A) : a^2 = 1 := by
    apply Subtype.ext
    exact mem_bot.mp (hd.le_bot ⟨A.pow_mem a.property 2,
      square_mem_pCore_of_quadratic hc A hq a a.property⟩)
  let : IsMulCommutative A := ⟨⟨fun a b => by
    have hi (x : A) : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs x)
    calc a*b = (a*b)⁻¹ := (hi _).symm
         _ = b*a := by rw [mul_inv_rev,hi,hi]⟩⟩
  exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs⟩
end Subgroup
