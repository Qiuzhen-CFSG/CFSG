module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.Model
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.FrattiniObstruction

/-!
# The remaining center–Frattini source question

A.3.6 explicitly allows homocyclic Sylow subgroups of higher exponent: its
proof on printed p.45 explains why it cannot force exponent `p` when the
quotient is `SL₂(5)` and `p > 5`. Proposition 1.2.1(4d), printed p.504,
adds `Z(L̄) = Φ(F*(L̄))` while referring only to A.3.6.

The fixed semidirect product in `CenterFrattiniSource.Model` has a normal
`C₁₂₁ × C₁₂₁` inverted by a complement element. If the complement order is
prime to eleven, the proved Fitting calculation identifies this subgroup
with `F*`, so the existing Frattini obstruction applies to the actual model.

`CenterFrattiniSource.Counterexample` now discharges the complement, SQTK,
C-component and full A.3.6 certificates. It proves a counterexample to the
intrinsic implication, retaining every common clause. This base module keeps
its original conditional API so the structure certificate can import it.

The counterexample has no asserted QTKE ambient realization. The Chapter 1
application still needs an ambient argument excluding the higher-exponent
inverted configuration. The separate `OmegaActions` development concerns the
actual action on Ω₁(Oₚ(B))/Φ(Ω₁(Oₚ(B))); it does not impose exponent p on Oₚ(B).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource

/-- The Frattini subgroup of the concrete normal vector subgroup is not central. -/
theorem kernel_frattini_not_central :
    ¬ (frattini kernel).map kernel.subtype ≤ center Candidate :=
  frattini_not_central_of_homocyclic_121_inversion kernel kernelEquiv
    inverter inverter_conjugates_kernel

/-- The concrete Fitting calculation discharges the abstract obstruction's
subgroup-isomorphism premise, conditional only on the complement order. -/
theorem not_centerFrattini_of_coprime
    (hc : Nat.Coprime 11 (Nat.card complement)) : ¬ CenterFrattini Candidate := by
  let e : generalizedFitting Candidate ≃*
      StandardHomocyclicCover (Fin 2) (11 ^ 2) :=
    (MulEquiv.subgroupCongr (generalizedFitting_eq_kernel_of_coprime hc)).trans kernelEquiv
  apply not_centerFrattini_of_homocyclic_121_inversion e inverter
  intro v
  exact inverter_conjugates_kernel
    ⟨v, (generalizedFitting_eq_kernel_of_coprime hc) ▸ v.property⟩

/-- The proposed complement order implies the failure of the additional equality.
Its order and the remaining source hypotheses are separate proof obligations. -/
theorem not_centerFrattini_of_complement_card
    (hc : Nat.card complement = 120) : ¬ CenterFrattini Candidate :=
  not_centerFrattini_of_coprime (by rw [hc]; decide)

end CFSG.Quasithin.Chapter1.Section02.CenterFrattiniSource
