module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.CompiledMarkedActions
public import Theory.SpecificGroups.Held.Model.FourPointBase

/-!
# Aligning the existing Held cover with the literal max5 subgroup

An explicit conjugator carries each generator of the existing four-generator
marking into the centralizer of max5First^4. The proved equality of that
centralizer with max5 supplies subgroup containment. The standard generator
b lies outside max5, and adjoining it recovers a from max5First = a*b^3.
These facts supply properness, marking alignment and generation for the
finite double-coset maximality proof in the parent module.

The conjugator combines the words in SylowOvergroups/MarkingFacts/TwoGroup
and TwoLocalCandidates/SylowContainment. The four commutation equations are
checked on Held's proved four-point base, using certified permutation tables.
All words preserve Held/Model/Source/README.md's inversion convention.
Source: ATLAS HeG1-p2058B0 and HeG1-max5W1; the consumer is the maximal
local used for Aschbacher–Smith E.1.14(4), printed p.214.
-/

@[expose] public section

open Subgroup
open Held Held.TwoLocalCandidates
open Held.LocalPairs.PairCoverage Held.LocalPairs.PairCoverage.SylowOvergroups
namespace Held.RankOneLocalPair.ConcreteMaximality

/-- The literal alignment from the existing marked subgroup to max5. -/
def conjugator : He :=
  wordEval a (localWord false)
    [(true, 1), (false, 1), (true, -2), (false, 1), (true, -4), (false, 1),
      (true, -1), (false, -1), (true, -1), (false, -1), (true, 1)] *
  wordEval a b [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1),
    (true, 2), (false, 1), (true, 1), (false, -1), (true, 1), (false, -1),
    (true, 1), (false, -1), (true, -1), (false, -1), (true, -2)]

open Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
open Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets

/-- The same alignment evaluated in the certified permutation tables. -/
def fastConjugator : Equiv.Perm (Fin 2058) :=
  wordEval fastA Cores.Tables0.p1
    [(true, 1), (false, 1), (true, -2), (false, 1), (true, -4), (false, 1),
      (true, -1), (false, -1), (true, -1), (false, -1), (true, 1)] *
  wordEval fastA fastB [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1),
    (true, 2), (false, 1), (true, 1), (false, -1), (true, 1), (false, -1),
    (true, 1), (false, -1), (true, -1), (false, -1), (true, -2)]

theorem fastConjugator_eq : fastConjugator = representation conjugator := by
  simp only [fastConjugator, conjugator, map_mul, map_wordEval, fastA_eq, fastB_eq,
    Cores.Tables0.p1_eq]
  rfl

def transport : MulAut He := MulAut.conj (conjugator⁻¹)

set_option maxRecDepth 4096 in
theorem representation_transport_marked (i : Fin 4) :
    representation (transport (markedGenerator i)) =
      fastConjugator⁻¹ * markedPermutation i * fastConjugator := by
  rw [transport, MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv,
    ← fastConjugator_eq, representation_markedGenerator]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem marked_commutes (i : Fin 4) :
    transport (markedGenerator i) * max5First ^ 4 =
      max5First ^ 4 * transport (markedGenerator i) := by
  apply Held.eq_of_four_point_images
  simp only [map_mul, representation_transport_marked,
    ← CentralInvolutionBounds.p2_eq_representation]
  fin_cases i <;> decide +kernel

/-- The transported old marking lies in the literal max5 subgroup. -/
theorem marked_le : markedSubgroup.map transport.toMonoidHom ≤ max5 := by
  rw [← InvolutionFixedData.TwoB.centralizer_eq_max5]
  rw [markedSubgroup, MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (marked_commutes i)

theorem generator_not_mem : b ∉ max5 := by
  intro hb
  have hc := mem_centralizer_singleton_iff.mp
    (InvolutionFixedData.TwoB.centralizer_eq_max5.symm ▸ hb)
  have he := congrArg (fun g : He => representation g 0) hc
  have hn : representation (b * max5First ^ 4) 0 ≠
      representation (max5First ^ 4 * b) 0 := by decide +kernel
  exact hn he

/-- max5 is a proper subgroup of the actual carrier. -/
theorem proper : max5 ≠ ⊤ := by
  intro h
  exact generator_not_mem (h ▸ mem_top b)

/-- Adjoining b to max5 generates the whole Held carrier. -/
theorem generation (K : Subgroup He) (hK : max5 ≤ K) (hb : b ∈ K) : K = ⊤ := by
  have ha : a ∈ K := by
    have h := K.mul_mem (hK max5First_mem) (K.inv_mem (K.pow_mem hb 3))
    simpa only [max5First, mul_inv_cancel_right] using h
  apply top_unique
  rw [← Held.closure_pair, closure_le]
  intro x hx
  rcases hx with rfl | hx
  · exact ha
  · obtain rfl := Set.mem_singleton_iff.mp hx
    exact hb

end Held.RankOneLocalPair.ConcreteMaximality
