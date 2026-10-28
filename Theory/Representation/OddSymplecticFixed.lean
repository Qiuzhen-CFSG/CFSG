module
public import Theory.Representation.BinaryOffender.Defs
public import Theory.LinearAlgebra.AlternatingFinrank

/-!
# Odd actors cannot fix a symplectic line

Averaging over an odd subgroup preserves its pairing with each fixed vector.
If its whole fixed space were a line, alternation would make that line radical
in the ambient form, contradicting nondegeneracy. The application to the native
M₂₂ ten-dimensional modules excludes their invariant symplectic forms.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender
open scoped BigOperators
namespace Representation.OddSymplecticFixed
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
/-- An odd-order subgroup preserving a nondegenerate alternating binary form
cannot have a one-dimensional fixed space. -/
theorem fixed_finrank_ne_one (ρ : Representation (ZMod 2) D V)
    (B : LinearMap.BilinForm (ZMod 2) V) (ha : B.IsAlt) (hn : B.Nondegenerate)
    (hp : ∀ g u w, B (ρ g u) (ρ g w) = B u w)
    (A : Subgroup D) [Finite A] (ho : Odd (Nat.card A)) :
    finrank (ZMod 2) (fixedSpace ρ A) ≠ 1 := by
  classical
  intro hd
  let : Fintype A := Fintype.ofFinite A
  have hne : fixedSpace ρ A ≠ ⊥ := by
    intro h
    rw [h,finrank_bot] at hd
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hd hv hv0
  apply hv0
  apply hn.1
  intro w
  let z : V := ∑ a : A, ρ a w
  have hz : z ∈ fixedSpace ρ A := by
    intro a
    change ρ a (∑ b : A, ρ b w) = ∑ b : A, ρ b w
    simp only [map_sum, ← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun b => rfl)
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hz)
  have hzero : B v z = 0 := by
    rw [← hc,map_smul,ha v,smul_zero]
  have hpair (a : A) : B v (ρ a w) = B v w := by
    simpa only [show ρ a v = v from hv a] using hp a v w
  have he : B v z = B v w := by
    change B v (∑ a : A, ρ a w) = _
    rw [map_sum]
    simp only [hpair,Finset.sum_const,Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
    have hc : (Fintype.card A : ZMod 2) = 1 := by
      simpa only [Nat.card_eq_fintype_card] using ho.natCast_zmod_two
    rw [hc,one_smul]
  exact he.symm.trans hzero
end Representation.OddSymplecticFixed
