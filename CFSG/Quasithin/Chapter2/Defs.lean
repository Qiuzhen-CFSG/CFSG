module

public import Theory.PGroupCore

/-!
# Subgroup families for the unique maximal 2-local case

These are the families in Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), Notations 2.2.4, 2.3.1,
2.3.4–2.3.5 and 2.3.11, pp. 520–527.

All subgroups are represented in the ambient group. `twoCore` is the image
of the intrinsic 2-core. The parameter `E` in the local families is the
collection `He` of subgroups of characteristic 2 from Definition 1.1.1.
Keeping this collection explicit lets the elementary selection arguments
be used before the Chapter 1 structure theorems are imported; applications
to the source must instantiate `E` with that collection.

`gammaStar` denotes the superscript-star family (first maximize the order
of `U`, then the 2-part of the local subgroup). `gammaMax` denotes the
subscript-star family (maximize only the latter 2-part). These are distinct
conditions in the source.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2

variable {G : Type*} [Group G]

/-- The ambient image of `O₂(H)`. -/
def twoCore (H : Subgroup G) : Subgroup G := (pCore 2 H).map H.subtype

/-- The nonidentity 2-subgroups, denoted `S₂(G)` in the source. -/
def twoSubgroups : Set (Subgroup G) := {U | U ≠ ⊥ ∧ IsPGroup 2 U}

/-- Notation 2.3.1: the three conditions (β₀), (β₁), (β₂). -/
def beta (M : Subgroup G) : Set (Subgroup G) :=
  {U | U ∈ twoSubgroups ∧ U ≤ M ∧
    (∀ V : Subgroup G, V ∈ twoSubgroups → U ≤ V → V ≤ M →
      Subgroup.normalizer (V : Set G) ≤ M) ∧
    twoCore M ⊓ Subgroup.centralizer (U : Set G) ≤ U}

/-- Notation 2.2.4, with `E` the characteristic-2 subgroups. -/
def delta (E : Set (Subgroup G)) (M : Subgroup G) : Set (Subgroup G) :=
  {D | D ∈ twoSubgroups ∧ Subgroup.normalizer (D : Set G) ∈ E ∧
    D ≤ M ∧ ¬ Subgroup.normalizer (D : Set G) ≤ M}

/-- The inclusion-maximal members of δ. -/
def deltaStar (E : Set (Subgroup G)) (M : Subgroup G) : Set (Subgroup G) :=
  {D | Maximal (· ∈ delta E M) D}

/-- Notation 2.3.4: the pairs `(U,Hᵤ)` in `𝒰(G)`. -/
def localPairs (E : Set (Subgroup G)) (M : Subgroup G) :
    Set (Subgroup G × Subgroup G) :=
  {P | P.1 ∈ beta M ∧ P.2 ∈ E ∧ twoCore P.2 ≠ ⊥ ∧ P.1 ≤ P.2 ∧ ¬ P.2 ≤ M}

/-- The first coordinates of the pairs in `𝒰(G)`. -/
def localBases (E : Set (Subgroup G)) (M : Subgroup G) : Set (Subgroup G) :=
  {U | ∃ K, (U, K) ∈ localPairs E M}

/-- The pairs `𝒰(H)` whose second coordinate lies in `H`. -/
def localPairsIn (E : Set (Subgroup G)) (M H : Subgroup G) :
    Set (Subgroup G × Subgroup G) :=
  {P | P ∈ localPairs E M ∧ P.2 ≤ H}

/-- Notation 2.3.5: the members of `𝒣` containing a pair in `𝒰(G)`. -/
def gamma (E : Set (Subgroup G)) (M : Subgroup G) : Set (Subgroup G) :=
  {H | twoCore H ≠ ⊥ ∧ (localPairsIn E M H).Nonempty}

/-- The order of a Sylow 2-subgroup of a finite subgroup. -/
noncomputable def twoPart (H : Subgroup G) : ℕ :=
  2 ^ (Nat.card H).factorization 2

/-- Those `H` containing a pair whose first coordinate has globally maximal order. -/
def gammaWithLargestBase (E : Set (Subgroup G)) (M : Subgroup G) :
    Set (Subgroup G) :=
  {H | H ∈ gamma E M ∧ ∃ P ∈ localPairsIn E M H,
    ∀ V ∈ localBases E M, Nat.card V ≤ Nat.card P.1}

/-- The superscript-star family in Notation 2.3.5. -/
def gammaStar (E : Set (Subgroup G)) (M : Subgroup G) : Set (Subgroup G) :=
  {H | H ∈ gammaWithLargestBase E M ∧
    ∀ K ∈ gammaWithLargestBase E M, twoPart K ≤ twoPart H}

/-- The subscript-star family in Notation 2.3.5. -/
def gammaMax (E : Set (Subgroup G)) (M : Subgroup G) : Set (Subgroup G) :=
  {H | H ∈ gamma E M ∧ ∀ K ∈ gamma E M, twoPart K ≤ twoPart H}

/-- The union of the two maximality families. -/
def gammaZero (E : Set (Subgroup G)) (M : Subgroup G) : Set (Subgroup G) :=
  gammaStar E M ∪ gammaMax E M

/-- Notation 2.3.11: the characteristic-2 members of `Γ`. -/
def gammaEven (E : Set (Subgroup G)) (M : Subgroup G) : Set (Subgroup G) :=
  gamma E M ∩ E

/-- Notation 2.3.11: the characteristic-2 members of `Γ₀`. -/
def gammaEvenZero (E : Set (Subgroup G)) (M : Subgroup G) : Set (Subgroup G) :=
  gammaZero E M ∩ E

end CFSG.Quasithin.Chapter2
