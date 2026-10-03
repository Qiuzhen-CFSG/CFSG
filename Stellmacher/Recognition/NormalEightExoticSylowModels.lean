module

public import Theory.SpecificGroups.MacWilliams.HallJankoRecognition
public import Theory.SpecificGroups.MacWilliams.UnitaryInvolutions
public import Theory.GroupTheory.PGroup.Omega
public import Stellmacher.Recognition.NormalEightExoticSylowOrder
public import Stellmacher.Recognition.NormalEightExoticHallGenerators

/-!
# Reduction of the central-two Sylow models to Hall–Janko generators

An elementary subgroup of order sixteen contributes fifteen involutions, so
it excludes the unitary presentation, which has exactly three. Consequently
the model dichotomy required in the central-omega-two branch is equivalent
to Hall–Janko recognition. The certified Hall–Janko presentation gives that
recognition from an order bound and a generating tuple satisfying its table.

The order bound and the construction of the tuple from the ambient simple
group hypotheses remain to be proved. The conditional assembly here does not
assert the unconditional MacWilliams theorem.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, printed p.386,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`;
MacWilliams, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace Stellmacher.Recognition.NormalEightExoticSylowModels

open Subgroup MacWilliamsSylow

/-- An elementary sixteen rules out the unitary presentation without any
assumption about central omega or normal elementary subgroups. -/
public theorem not_unitary_of_elementary_sixteen
    {P : Type*} [Group P] [Finite P]
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    ¬ Nonempty (P ≃* UnitarySylow) := by
  classical
  rintro ⟨e⟩
  let f : {b : B // b ≠ 1} → {x : UnitarySylow // orderOf x = 2} := fun b =>
    ⟨e b.val, (e.orderOf_eq b.val).trans (orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian b.val.val b.val.property)
      (fun h => b.property (Subtype.ext h)))⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)
  let : Fintype B := Fintype.ofFinite B
  have hc : Nat.card {b : B // b ≠ 1} = Nat.card B - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [Nat.card_eq_fintype_card]
  have hle := Nat.card_le_card_of_injective f hf
  rw [hc, hB, unitarySylow_involution_count] at hle
  omega

/-- In the actual sixteen-subgroup branch, only the Hall–Janko member of
the requested dichotomy can occur. -/
public theorem models_iff_hallJanko
    {P : Type*} [Group P] [Finite P]
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    (Nonempty (P ≃* HallJankoSylow) ∨ Nonempty (P ≃* UnitarySylow)) ↔
      Nonempty (P ≃* HallJankoSylow) := by
  exact or_iff_left (not_unitary_of_elementary_sixteen B hB)

/-- The remaining numerical and generator constructions feed the requested
model dichotomy directly. -/
public theorem models_of_hallJanko_generators
    {P : Type*} [Group P] (hcard : 128 ≤ Nat.card P)
    (x : Fin 7 → P) (hrel : Relations hallJankoTable x)
    (hgen : Subgroup.closure (Set.range x) = ⊤) :
    Nonempty (P ≃* HallJankoSylow) ∨ Nonempty (P ≃* UnitarySylow) :=
  Or.inl (nonempty_hallJanko_equiv_of_generators hcard x hrel hgen)

/-- The central-omega-two branch of Janko--Thompson 1.3 gives one of the two
MacWilliams Sylow presentations.  The order calculation and the explicit
Hall--Janko generating frame are supplied by the preceding recognition
modules; the elementary sixteen rules out the unitary presentation after the
Hall--Janko recognition is applied. -/
public theorem models_of_central_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G)
    (hnorm : Subgroup.normalizer (S : Set G) ≠
      (S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G))
    (hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(Stellmacher.Recognition.NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 →
      orderOf v = 2 → IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    Nonempty (S ≃* MacWilliamsSylow.HallJankoSylow) ∨
      Nonempty (S ≃* MacWilliamsSylow.UnitarySylow) := by
  have hcard := NormalEightExoticSylowOrder.card_eq_128
    hns hN S hnorm hZ hno W hW hunique hfused B hB
  obtain ⟨x, hrel, hgen⟩ := NormalEightExoticHallGenerators.exists_generators
    S hZ hno W hW hunique hfused B hB hcard
  exact models_of_hallJanko_generators (by omega) x hrel hgen

end Stellmacher.Recognition.NormalEightExoticSylowModels
