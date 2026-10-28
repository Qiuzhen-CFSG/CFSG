module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J2.Placement.WordChecks.Tables

/-!
# Order-five obstructions for the J₂ placement sieve

Each retained obstruction outside the first six representatives has fifth power
one and moves point zero in the degree-100 action. These pointwise kernel checks
prove exact order five in the actual carrier, using faithfulness of inclusion.

The words and numbering are those of `Placement.Representatives`; its
`obstruction_mem` places these elements in the overgroups used by the parent.
Source: Aschbacher–Smith, proof of 1.3.4, printed p.511/PDF p.528, and GLS3
Table 5.3g. The ATLAS source attribution accompanies the carrier.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.WordChecks
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics
open GeneratorPair GeneratorPair.SecondOrbitCertificate Theory.GroupTheory
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

def localTable (i : Fin 72) (j : Fin 8) : Equiv.Perm (Fin 100) :=
  if h : j.val < 7 then sTable ⟨j.val, h⟩ else repTable i

def obstructionTable (i : Fin 72) : Equiv.Perm (Fin 100) :=
  evalWord (localTable i) (obstructionWords[i.val]!)

theorem obstruction_eq (i : Fin 72) :
    inclusion (obstruction i) = obstructionTable i := by
  unfold obstruction obstructionTable
  rw [map_evalWord]
  apply congrArg (fun g : Fin 8 → Equiv.Perm (Fin 100) =>
    evalWord g (obstructionWords[i.val]!))
  funext j
  unfold localGenerator localTable
  split
  · exact s_eq _
  · exact rep_eq i

/-- The fifth powers fix all one hundred points. -/
theorem obstructionTable_fifth : ∀ i : Fin 72, 6 ≤ i.val → ∀ x : Fin 100,
    (obstructionTable i ^ 5) x = x := by
  apply allFin
  decide +kernel

/-- All sixty-six words move point zero. -/
theorem obstructionTable_moves_zero : ∀ i : Fin 72, 6 ≤ i.val →
    obstructionTable i 0 ≠ 0 := by
  apply allFin
  decide +kernel

/-- The retained words have order exactly five in the actual carrier. -/
theorem obstruction_order_five (i : Fin 72) (hi : 6 ≤ i.val) :
    orderOf (obstruction i) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply inclusion_injective
    rw [map_pow, map_one, obstruction_eq]
    exact Equiv.ext (obstructionTable_fifth i hi)
  · intro h
    have hh := congrArg inclusion h
    rw [obstruction_eq, map_one] at hh
    exact obstructionTable_moves_zero i hi (congrArg (fun p : Equiv.Perm (Fin 100) => p 0) hh)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J2Placement.WordChecks
