module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Common
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.AllPrimes
public import Theory.SpecificGroups.SU3.OddPrimeInvolutionComponent
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# The odd-prime PSU₃ parameter in the marked involution classification

The original marked action induces an involution on the literal central
quotient. Its full fixed group has characteristic two, and it fixes an actual
Sylow two-subgroup pointwise. The universal odd-prime Sylow-fixer theorem
makes this action inner. When p > 3 its fixed group has a genuine SL₂(p)
component, contradicting characteristic two. Thus only p = 3 remains.

This discharges exactly the `hunitary` premise of
`MarkedInvolution.odd_of_parameters_and_centers`. The action at p = 3 and
the independent cover exclusion are handled by their existing producers.
Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.503 / PDF p.520.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
variable {α : MulAut L} {P : Sylow 2 L}

/-- The characteristic-two full fixed group excludes every PSU₃(p) parameter
larger than three, for the original marked involution and its central quotient. -/
theorem MarkedInvolution.not_unitary_three_gt_three
    (d : MarkedInvolution α P) (p : ℕ) (hp : p.Prime) (ho : Odd p) (hlarge : 3 < p)
    (h : ClassicalGroup.IsPSU (L ⧸ center L) 3 p) : False := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hF, hfin, J, hc, hconj, ⟨e⟩⟩ := h
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective
      (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  obtain ⟨horder, hchar, Q, hQ⟩ := d.centralQuotient_model_inputs e
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using
      FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hc) (by simpa only [pow_one] using hconj)
  obtain ⟨z, hz⟩ := HermitianForm.OddPrimeSylow.inner_of_involutive_fixing_sylow
    J hp ho hc hfixed Q (MulAut.centralQuotientAction e α)
    (horder ▸ pow_orderOf_eq_one _) hQ
  have hzo : orderOf z = 2 := by
    rw [← MulAut.conj_orderOf_of_center_eq_bot
      (Subgroup.center_eq_bot_of_simple_perfect (G := ProjectiveSpecialUnitaryMatrixGroup J)),
      ← hz]
    exact horder
  rw [hz, MulAut.fixedSubgroup_conj] at hchar
  obtain ⟨D, _, hD, _⟩ := Matrix.SU3.OddPrimeComponent.involution_centralizer_has_sl2_component
    p ho hlarge F J hc hconj z hzo
  exact not_isComponent_of_twoCore hchar D hD

/-- The exact unitary parameter input to the odd-family source assembly. -/
theorem MarkedInvolution.unitary_three_parameter
    (d : MarkedInvolution α P) (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (h : ClassicalGroup.IsPSU (L ⧸ center L) 3 p) : p = 3 := by
  by_contra hn
  have htwo := hp.two_le
  have hodd := Nat.odd_iff.mp ho
  exact d.not_unitary_three_gt_three p hp ho (by omega) h

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
