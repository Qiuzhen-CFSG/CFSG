module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Input
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases.Linear
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases.Symplectic
public import Theory.Representation.G2NaturalTransitivity

/-!
# The natural field-module sieve for 15.3.58

`NaturalCases.Alternative` retains the exact natural actions and original
actor-rank bounds in G.9.3(6),(8),(9),(10), independently of `SourceData`.
All four branches are excluded using the source nonsingular quadratic form
and the actual model orbits. Nonzero-vector transitivity rules out an invariant
nonsingular binary quadratic form in dimension greater than two; the smallest
derived symplectic case is instead excluded by its degree four. The derived G₂
orbit theorem includes the proper derived subgroup over the field of order two.

`exclude` discharges every model premise in the conditional reduction below.
The argument applies at all field parameters, without a field-degree bound or
membership of the marked involution in the component join.

Source: Aschbacher--Smith, G.9.3, printed pp.353--357, and the proof of
15.3.58, printed p.1149.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases

open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
attribute [local instance] ZMod.algebra

universe u v f
variable {H : Type u} {W : Type v} [Group H] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- All four source cases are excluded once the intrinsic G₂ orbit theorem is
available. The SL₂, SL₃, and Sp₄′ calculations are discharged in this module's
imports; no model-exclusion premise is used for those three branches. -/
theorem exclude_of_g2_transitivity
    (hg2 : ∀ (F : Type f) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      ∀ x y : Atlas.G2.Natural.Space F, x ≠ 0 → y ≠ 0 →
        ∃ g : commutator (Atlas.G2.Model F), Atlas.G2.Natural.derivedAction F g x = y)
    (h : SourceData ρ X T v s) (ha : Alternative.{u, v, f} ρ K (s + 1)) : False := by
  cases ha with
  | rankOne n hn hc hd hb hnat => exact h.not_natural_rankOne K hnat
  | linearThree n hn hc hd hb hnat => exact h.not_natural_linearThree K hnat
  | symplecticFour n hn hc hd hb hnat =>
      exact h.not_natural_symplecticFour K hc hd hnat
  | @g2 F _ _ _ n hn hc hd hb hnat =>
      exact h.not_nonzero_transitive_model K (G2Recognition.derivedNaturalBinary F)
        (hg2 F inferInstance inferInstance inferInstance) hnat

/-- The natural field-module cases (6), (8), (9), and (10) of G.9.3 are
impossible in the irreducible branch of 15.3.58, with the original actor rank
`s + 1`. All model orbit theorems are discharged. The quadratic obstruction
already follows from `SourceData`, so no component-structure property is needed. -/
theorem exclude (h : SourceData ρ X T v s) (_hK : ComponentData ρ K)
    (ha : Alternative.{u, v, f} ρ K (s + 1)) : False :=
  exclude_of_g2_transitivity
    (fun F _ _ _ => Atlas.G2.Natural.derivedAction_transitive F) h ha

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases
