module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21.OddOrders
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21

/-!
# Applying the odd spectrum to the degree-21 character assembly

The odd-spectrum theorem discharges precisely the odd-structure premise of
`nonempty_of_character_and_odd_structure`, under the original local inputs.
The actual character, its local values, minimum degree and uniqueness remain
explicit premises owned by the character construction. This application is a
separate extension so that `Degree21` can itself import `OddOrders`.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 7, pp.15–16,
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Discharge the odd-structure assumption of the actual degree-21 consumer. -/
public theorem nonempty_of_character_and_local_structure [IsSimpleGroup G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (hcard : Nat.card G = 443520)
    (hN3 : ∀ P : Sylow 3 G, Nat.card (normalizer (P : Set G)) = 72)
    (χ : ClassFunction G) (hχ : IsIrreducibleCharacter χ) (hloc : HasLocalValues D k χ)
    (hmin : ∀ θ : ClassFunction G, IsIrreducibleCharacter θ → θ ≠ 1 →
      (21 : ℝ) ≤ (θ 1).re)
    (huniq : ∀ θ : ClassFunction G, IsIrreducibleCharacter θ → θ 1 = 21 → θ = χ) :
    Nonempty (Degree21Character G) :=
  nonempty_of_character_and_odd_structure D k L hcard χ hχ hloc hmin huniq
    (odd_orders D k L hcard hN3)


end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.Degree21
