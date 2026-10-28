module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.BCensus
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.DerivedNormalizer

/-!
# Assembly of the actual local subgroups for Janko's Lemma 17

The original local data now construct the common order-three actor, the
literal subgroup `X = (N(F))'` of order 960, and `B = EQ*` inside X. The
complete census of B is proved. The remaining inputs are the census of X
and the involution `z*` outside N(F), with the conjugate intersection B and
the census of `Y = EQ*Z*`.

The theorem below assembles those still-explicit inputs into the shared
`LocalConfiguration`. The disjoint double-coset estimate proves the generated
subgroup has at least 20160 elements. No properness, index or action is
assumed. This conditional assembly does not assert existence of the remaining
reflection and census inputs from the source hypotheses.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, Section 8, Lemma 17, pp.16--17;
DOI 10.1016/0021-8693(68)90002-1.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- Assemble the local configuration from the remaining X census and source
reflection geometry. Their existence remains with the source assembly owner. -/
public theorem localConfiguration_of_reflection (L : LocalAnalysisData D k)
    (w : FusedNineIntersectionActor D k) (z : G)
    (hz : z ∉ normalizer (CaseII.F D k : Set G))
    (hinter : X D k ⊓ (X D k).map (MulAut.conj z).toMonoidHom = B D k w)
    (hXcount : ∀ n : ℕ, Nat.card {x : X D k // orderOf x = n} =
      localOrderCount 75 320 180 384 n)
    (hYcard : Nat.card (Y D k w z) = 96)
    (hYcount : ∀ n : ℕ, Nat.card {y : Y D k w z // orderOf y = n} =
      localOrderCount 27 32 36 0 n) : Nonempty (LocalConfiguration G) := by
  refine ⟨{
    X := X D k
    Y := Y D k w z
    B := B D k w
    B_le_X := B_le_X D k L w
    B_le_Y := le_sup_left
    X_card := X_card D k L w
    Y_card := hYcard
    B_card := B_card D k w
    X_count := hXcount
    Y_count := hYcount
    B_count := B_count D k w
    generated_card_lower := ?_ }⟩
  apply generated_card_lower_of_conjugate_intersection (X D k) (Y D k w z)
    (X_card D k L w) z
    ((show zpowers z ≤ Y D k w z from le_sup_right) (mem_zpowers z))
    (fun hzX => hz (X_le_normalizer_F D k hzX))
  rw [hinter, B_card]

end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups
