module

public import Theory.AlgebraicGroup.RootSystems.TypeD4RestrictedWeights

/-!
# Exchanged weight pairs for the two triality involutions

The central reflection and the product of the three arm reflections each
exchange at least two disjoint pairs in every nonzero binary D4 Weyl orbit.
For the three nonzero diagram-fixed weights, six disjoint pairs suffice.
The entries are indices into the existing checked list of reflection words;
only the small distinctness certificates are evaluated here.

These are weight-lattice statements. The representation consumer transports
them to actual nonzero torus weight spaces and then to operator displacement.
Source: GLS3 §§1.14 and 2.8; Guralnick–Malle II, Lemma 8.6.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.BasicDisplacement

/-- The central reflection, or the commuting three-arm reflection. -/
def reflect (short : Bool) (a : Weight) : Weight :=
  if short then reflection 0 (reflection 2 (reflection 3 a)) else reflection 1 a

/-- Indices of six witnesses; only the first two are used away from fixed weights. -/
def pairIndices (short : Bool) (a : BasicWeight) : Fin 6 → Fin 25 :=
  match short, a 0, a 1, a 2, a 3 with
  | false, false, false, false, false => ![0, 0, 0, 0, 0, 0]
  | false, false, false, false, true => ![4, 21, 21, 21, 21, 21]
  | false, false, false, true, false => ![3, 19, 19, 19, 19, 19]
  | false, false, false, true, true => ![3, 4, 7, 12, 14, 19]
  | false, false, true, false, false => ![0, 5, 6, 7, 9, 12]
  | false, false, true, false, true => ![0, 4, 5, 6, 7, 9]
  | false, false, true, true, false => ![0, 3, 5, 6, 7, 9]
  | false, false, true, true, true => ![0, 3, 4, 5, 6, 7]
  | false, true, false, false, false => ![2, 20, 20, 20, 20, 20]
  | false, true, false, false, true => ![2, 4, 6, 12, 15, 20]
  | false, true, false, true, false => ![2, 3, 5, 14, 15, 19]
  | false, true, false, true, true => ![2, 3, 4, 5, 6, 7]
  | false, true, true, false, false => ![0, 2, 5, 6, 7, 9]
  | false, true, true, false, true => ![0, 2, 4, 5, 6, 7]
  | false, true, true, true, false => ![0, 2, 3, 5, 6, 7]
  | false, true, true, true, true => ![0, 2, 3, 4, 5, 6]
  | true, false, false, false, false => ![0, 0, 0, 0, 0, 0]
  | true, false, false, false, true => ![0, 10, 14, 23, 23, 23]
  | true, false, false, true, false => ![0, 8, 12, 23, 23, 23]
  | true, false, false, true, true => ![0, 3, 8, 10, 11, 12]
  | true, false, true, false, false => ![1, 2, 3, 4, 8, 10]
  | true, false, true, false, true => ![0, 1, 2, 3, 4, 8]
  | true, false, true, true, false => ![0, 1, 2, 3, 4, 8]
  | true, false, true, true, true => ![0, 1, 2, 3, 4, 8]
  | true, true, false, false, false => ![0, 8, 12, 23, 23, 23]
  | true, true, false, false, true => ![0, 2, 8, 10, 11, 12]
  | true, true, false, true, false => ![0, 2, 8, 10, 11, 12]
  | true, true, false, true, true => ![0, 2, 3, 4, 8, 10]
  | true, true, true, false, false => ![0, 1, 2, 3, 4, 8]
  | true, true, true, false, true => ![0, 1, 2, 3, 4, 8]
  | true, true, true, true, false => ![0, 1, 2, 3, 4, 8]
  | true, true, true, true, true => ![0, 1, 2, 3, 4, 8]

/-- Original and exchanged weights, retaining the exact reflection-word witness. -/
def pairWeight (short : Bool) (a : BasicWeight) (i : Fin 6) : Weight :=
  wordAction (coefficient a) (words[pairIndices short a i])

def twoWeights (short : Bool) (a : BasicWeight) : Fin 2 ⊕ Fin 2 → Weight :=
  Sum.elim (fun i => pairWeight short a (Fin.castLE (by decide) i))
    (fun i => reflect short (pairWeight short a (Fin.castLE (by decide) i)))

def sixWeights (short : Bool) (a : BasicWeight) : Fin 6 ⊕ Fin 6 → Weight :=
  Sum.elim (pairWeight short a) (fun i => reflect short (pairWeight short a i))

/-- Four distinct weights give two independent displacement vectors. -/
theorem twoWeights_injective : ∀ (short : Bool) (a : BasicWeight),
    a ≠ zeroWeight → Function.Injective (twoWeights short a) := by
  decide +kernel

/-- Twelve distinct weights give six independent displacement vectors. -/
theorem sixWeights_injective : ∀ (short : Bool) (a : BasicWeight),
    a ≠ zeroWeight → diagramAction a = a → Function.Injective (sixWeights short a) := by
  decide +kernel

/-- Each selected starting weight belongs to the original reflection-invariant support. -/
theorem pairWeight_mem {S : Set Weight}
    (hS : ∀ i a, a ∈ S → reflection i a ∈ S)
    {a : BasicWeight} (ha : coefficient a ∈ S) (short : Bool) (i : Fin 6) :
    pairWeight short a i ∈ S :=
  wordAction_mem hS ha _

end Triality.RestrictedWeights.BasicDisplacement
