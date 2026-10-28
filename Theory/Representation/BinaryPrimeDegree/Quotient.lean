module

public import Theory.Representation.BinaryPrimeDegree
public import Theory.Representation.BinaryOffender.QuadraticImageBound

/-!
# Prime-order degree bounds from quotients

A prime-order element in an actual quotient forces the same prime to divide
the order of the original finite group. The binary general-linear order formula
therefore bounds the multiplicative order of two by every faithful binary degree.
This works for central covers without classifying their centers or lifting an
element with exactly the same order.

Source application: Aschbacher–Smith, B.1.13, printed pp.73–74; the elementary
prime-degree argument is G.7.1(1), printed p.347.
-/

public section
namespace Representation.BinaryPrimeDegree

variable {G S V : Type*} [Group G] [Finite G] [Group S]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A prime-order element in any surjective image bounds faithful binary degrees. -/
theorem orderOf_le_finrank_of_quotient_element
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (q : G →* S) (hq : Function.Surjective q)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : S) (hx : orderOf x = p) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  let : Finite S := Finite.of_surjective q hq
  apply orderOf_le_finrank ρ hρ hp hp2
  exact (hx ▸ orderOf_dvd_natCard x).trans (Subgroup.card_dvd_of_surjective q hq)

/-- Specialization through an actual central-quotient equivalence. -/
theorem orderOf_le_finrank_of_central_quotient
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (e : G ⧸ Subgroup.center G ≃* S)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (x : S) (hx : orderOf x = p) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V :=
  orderOf_le_finrank_of_quotient_element ρ hρ
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center G)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hp hp2 x hx

section KernelDetection
open Subgroup Representation.BinaryOffender
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- If the representation kernel lies in N, a prime divisor of |H:N| bounds
the binary degree. Source: Aschbacher–Smith E.2.13(4), printed p.225. -/
theorem orderOf_le_finrank_of_kernel_le
    (ρ : Representation (ZMod 2) H W) (N : Subgroup H) (hk : ρ.ker ≤ N)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdiv : p ∣ N.index) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) W := by
  have he : ρ.ker.index = Nat.card (actionImage ρ) := by
    have ht : (actionHom ρ).range = ⊤ :=
      MonoidHom.range_eq_top.mpr ρ.asGroupHom.rangeRestrict_surjective
    rw [← actionHom_ker_eq ρ, index_ker, ht]
    exact Nat.card_congr (Subgroup.topEquiv :
      (⊤ : Subgroup (actionImage ρ)) ≃* actionImage ρ).toEquiv
  apply orderOf_le_finrank (imageRepresentation ρ) (imageRepresentation_injective ρ) hp hp2
  rw [← he]
  exact hdiv.trans (index_dvd_of_le hk)
end KernelDetection

end Representation.BinaryPrimeDegree
