module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.FixedSpace
public import Theory.Representation.BinaryAlternatingSevenFixedPoints

/-!
# A three-cycle witness in the exceptional A₇ module

A three-cycle acts without nonzero fixed vectors in every faithful
four-dimensional binary representation of A₇. Applying that intrinsic
calculation through a chosen model of U/C_U(K) gives the source centralizer
comparison whenever the actual image of Lᵥ contains such a cycle.

The existence of this cycle is an explicit marking premise. This module
does not classify the three possible source actors in the line normalizer,
and does not identify an arbitrary order-three element with a three-cycle.
In particular it does not replace the whole exceptional-A₇ case analysis.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 13.6.22,
printed p.932; the representation calculation is used also in I.1.6(8).
-/

public section
open Subgroup Representation
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {L K U : Subgroup G} {v : G}

/-- A literal three-cycle in the actor image suffices on the exceptional module. -/
theorem exceptionalSeven_centralizer_eq_of_threeCycle
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod 2) V = 4)
    (m : ConjugationQuotientModel K U ρ) (hLK : Lv L v ≤ K)
    (hcycle : ∃ d : Lv L v,
      Equiv.Perm.IsThreeCycle (m.actor ⟨d, hLK d.property⟩ : Equiv.Perm (Fin 7))) :
    U ⊓ centralizer (Lv L v : Set G) = U ⊓ centralizer (K : Set G) := by
  obtain ⟨d, hd⟩ := hcycle
  apply m.centralizer_eq (Lv L v) hLK
  intro w hw
  exact binaryAlternatingSeven_threeCycle_fixedPointFree ρ hρ hdim
    (m.actor ⟨d, hLK d.property⟩) hd w (hw d)

/-- Application with the literal checked quotient, retaining the same actor and cycle. -/
theorem exceptionalSeven_checked_centralizer_eq_of_threeCycle [Finite G]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod 2) V = 4)
    (m : ConjugationQuotientModel K U ρ) (hLK : Lv L v ≤ K) (hv : v ^ 2 = 1)
    (hcycle : ∃ d : Lv L v,
      Equiv.Perm.IsThreeCycle (m.actor ⟨d, hLK d.property⟩ : Equiv.Perm (Fin 7))) :
    checkedImage v U ⊓ centralizer (checkedImage v (Lv L v) : Set (Gcheck v)) =
      checkedImage v U ⊓ centralizer (checkedImage v K : Set (Gcheck v)) :=
  checked_centralizer_eq_of_ambient L K U v hLK hv
    (exceptionalSeven_centralizer_eq_of_threeCycle ρ hρ hdim m hLK hcycle)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
