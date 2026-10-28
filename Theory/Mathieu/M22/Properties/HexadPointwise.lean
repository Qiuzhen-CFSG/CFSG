module
public import Theory.Mathieu.M22.Properties.ElementarySylowFixers
public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads

/-!
# Pointwise fixers of actual M₂₂ hexad stabilizers

The pointwise fixer of a Sylow two-subgroup is already inner. An inner
fixer of a full hexad lies in its elementary translation kernel; a nonidentity
such element would have a centralizer of order 384 containing the hexad
stabilizer of order 5760. Thus every automorphism fixing the hexad is trivial.

This is the model step for the binary-cover ambient Frattini argument in
Aschbacher--Smith 2.3.9(7), p.526. Both subgroups are the native M₂₂ carriers.
-/

open scoped Pointwise
public section
namespace Sporadic.Mathieu
open Subgroup

theorem m22_hexad_centralizer_eq_bot {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    centralizer (MulAction.stabilizer M22 B : Set M22) = ⊥ := by
  apply bot_unique
  intro g hg
  by_contra hne
  have hne : g ≠ 1 := hne
  have hk : g ∈ m22HexadPointwiseKernel B :=
    m22HexadPointwiseKernel_selfCentralizing hB
      (centralizer_le (m22HexadPointwiseKernel_le B) hg)
  let := m22HexadPointwiseKernel_elementaryAbelian hB
  have ho : orderOf g = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian g hk) hne
  have hle : MulAction.stabilizer M22 B ≤ centralizer ({g} : Set M22) :=
    fun x hx => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hg x hx)
  have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  rw [m22Hexad_stabilizer_card hB,M22FourNormalizers.involution_centralizer_card g ho] at hc
  omega

theorem m22_automorphism_eq_one_of_fixes_hexad {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (S : Sylow 2 M22) (hSI : (S : Subgroup M22) ≤ MulAction.stabilizer M22 B)
    (a : MulAut M22) (hfix : ∀ x ∈ MulAction.stabilizer M22 B, a x = x) : a = 1 := by
  obtain ⟨g,rfl⟩ := M22SylowPointwise.automorphism_inner_of_fixes_sylow a S
    (fun x hx => hfix x (hSI hx))
  have hg : g ∈ centralizer (MulAction.stabilizer M22 B : Set M22) := by
    intro x hx
    exact (mul_inv_eq_iff_eq_mul.mp (hfix x hx)).symm
  rw [m22_hexad_centralizer_eq_bot hB] at hg
  simpa only [show g = 1 from hg] using (map_one (MulAut.conj (G := M22)))
end Sporadic.Mathieu
