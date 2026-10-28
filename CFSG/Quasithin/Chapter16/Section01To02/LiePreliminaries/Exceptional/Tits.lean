module

public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.Basic
public import Theory.SpecificGroups.Tits.SylowPointwiseInner

/-!
# The Tits pointwise Sylow-centralizer case

The pointwise stabilizer of the certified Tits Sylow subgroup consists of the
identity and conjugation by its central involution. Sylow conjugacy and the
certified Parrott comparison give the same innerness result on the source
carrier. Faithfulness of the action on a perfect central quotient lifts it to
a component. This includes arbitrary two-power automorphisms, without an
order restriction.

This proves the innerness part of the Tits case of Aschbacher–Smith 16.1.6,
printed p.1172. The root identification and the exhaustive involution table
of 16.1.4, printed p.1171, remain separate model calculations. In particular,
no odd-order assertion about the Tits outer automorphism group is used.
-/

public section
namespace CFSG.Quasithin.Chapter16.LiePreliminaries
open Subgroup Theory.GroupTheory

variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]

/-- The Tits case of the innerness assertion of 16.1.6, even for arbitrary
Sylow-fixing automorphisms of a perfect central cover. -/
theorem tits_sylow_fixing_inner (hodd : pPrimeCore 2 L = ⊥)
    (e : (L ⧸ pCore 2 L) ≃* Tits.ParrottGroup)
    (P : Sylow 2 L) (r : MulAut L) (hr : ∀ x ∈ P, r x = x) :
    ∃ x ∈ P, r = MulAut.conj x :=
  MulAut.fixing_sylow_inner_of_centralQuotient
    ((centerQuotientEquivTwoCore hodd).trans e)
    Tits.SylowPointwiseInner.parrott_fixing_sylow_inner P r hr

end CFSG.Quasithin.Chapter16.LiePreliminaries
