module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.CoreCandidates
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.Parabolics
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity.MarkedAction

/-!
# Residual rigidity for the actual Ree and Tits first parabolics

An embedded actual first parabolic H contains a Sylow two-subgroup of Mc.
Assume its two-core is O₂(Mc), its derived centralizer F is normal in Mc,
and its marked representation extends faithfully to Mc/F. Then H = Mc,
and the literal embedded two-residual equals O²(Mc).

The translation identification constructs the faithful action of Mc/Q on the
actual Q/F, with its conjugation equation. Cyclic Sylow-two structure comes
from the actual order-twenty quotient in both models. Burnside transfer and
the checked odd-order theorem make the quotient residual odd and solvable.
A larger residual would have order fifteen and act regularly. Local involution
fusion would then give an H-orbit of length fifteen, contrary to 3 ∤ |H|.
This is the orbit-counting form of the source's final Frattini contradiction.

Residuals always use their images under the literal quotient maps; the proof
does not assume Q ≤ O²(H), which the full-Ree root character disproves.
The earlier core and ambient-action construction remain with the source
assembly owner. The centralizer hypothesis is retained in the application
interfaces; the supplied faithful action already suffices for this last step.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.989 (PDF p.1006), with
Aschbacher (1982), (3.2.11), supplied by the verified concrete orbit theorems.
The actual Tits first quotient has order twenty, as in Parrott (1972), p.672.
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity
open Subgroup ReeTwo.ParabolicConcrete ReeTwo.Centralizer
open Theory.LinearAlgebra.BinaryFivePointStabilizer
open Tits.ExceptionalParabolics

/-- Full-Ree rigidity, with the literal local and ambient two-residuals. -/
public theorem ree_rigidity {M : Type*} [Group M] [Finite M]
    (i : FullRee.first →* M) (hi : Function.Injective i)
    (hcore : pCore 2 M = reeQ.map i)
    (_hcentral : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (S : Sylow 2 M) (hS : (S : Subgroup M) ≤ i.range)
    [(reeF.map i).Normal]
    (ρ : M ⧸ reeF.map i →* stabilizer markedVector) (hρ : Function.Injective ρ)
    (hres : ∀ h : FullRee.first,
      ρ (QuotientGroup.mk' (reeF.map i) (i h)) = reeRepresentation h) :
    i.range = ⊤ ∧ (pResidual 2 FullRee.first).map i = pResidual 2 M := by
  have hthree : ¬ 3 ∣ Nat.card FullRee.first := by
    have hc : Nat.card reeQ * Nat.card (FullRee.first ⧸ reeQ) = Nat.card FullRee.first :=
      reeQ.card_mul_index
    rw [reeQ_card, ree_quotient_card] at hc
    rw [← hc]
    decide
  have htop := range_eq_top_of_extended_marked_action markedVector markedVector_ne_zero
    derivedSpace_finrank reeQ reeF reeF_le_Q reeRepresentation ree_core_representation_image
    i hi (pCore 2 M) hcore.symm ρ hρ hres ree_quotient_card ree_quotient_sylow_cyclic
    hthree S hS ree_exists_involution ree_involutions_isConj
  exact ⟨htop, map_pResidual_of_surjective 2 i (MonoidHom.range_eq_top.mp htop)⟩

/-- Tits rigidity for the actual mixed-kernel parabolic, with core of order 512. -/
public theorem tits_rigidity {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.first →* M) (hi : Function.Injective i)
    (hcore : pCore 2 M = titsQ.map i)
    (_hcentral : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (S : Sylow 2 M) (hS : (S : Subgroup M) ≤ i.range)
    [(titsF.map i).Normal]
    (ρ : M ⧸ titsF.map i →* stabilizer markedVector) (hρ : Function.Injective ρ)
    (hres : ∀ h : Tits.ExceptionalParabolics.first,
      ρ (QuotientGroup.mk' (titsF.map i) (i h)) = titsRepresentation h) :
    i.range = ⊤ ∧ (pResidual 2 Tits.ExceptionalParabolics.first).map i = pResidual 2 M := by
  have hthree : ¬ 3 ∣ Nat.card Tits.ExceptionalParabolics.first := by
    have hc : Nat.card titsQ * Nat.card (Tits.ExceptionalParabolics.first ⧸ titsQ) =
        Nat.card Tits.ExceptionalParabolics.first := titsQ.card_mul_index
    rw [titsQ_card, tits_quotient_card] at hc
    rw [← hc]
    decide
  have htop := range_eq_top_of_extended_marked_action markedVector markedVector_ne_zero
    derivedSpace_finrank titsQ titsF titsF_le_Q titsRepresentation tits_core_representation_image
    i hi (pCore 2 M) hcore.symm ρ hρ hres tits_quotient_card tits_quotient_sylow_cyclic
    hthree S hS tits_exists_involution tits_involutions_isConj
  exact ⟨htop, map_pResidual_of_surjective 2 i (MonoidHom.range_eq_top.mp htop)⟩

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity
