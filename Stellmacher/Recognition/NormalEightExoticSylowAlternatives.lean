module

public import Stellmacher.Recognition.NormalEightExoticRecognition
public import Stellmacher.Recognition.NormalEightExoticSylowModels
public import Stellmacher.Recognition.HallJankoTrivialSylowAutomizer
public import Theory.SpecificGroups.MacWilliams.UnitaryInvolutions
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Assembly of the exotic-branch Sylow alternatives

An elementary sixteen excludes the small dihedral exceptions in JT 1.3.
The conditional assembly combines recognition into the two MacWilliams
presentations with the ambient centralizer theorem JT 1.5; the unitary
presentation has exactly three involutions.

For the actual marked N₂ configuration, the central-two recognition theorem
supplies the models. The Hall–Janko fusion and transfer exclusion contradicts
that model directly under the consumer hypotheses. Thus the final alternative
is unconditional here, without the general ambient centralizer theorem or a
global elementary-rank bound.

Source: Janko–Thompson, Math. Z. 113 (1970), 1.3 and 1.5, printed p.386,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace Stellmacher.Recognition.NormalEightExoticRecognition

open Subgroup MacWilliamsSylow

/-- The subgroup of order sixteen already excludes all small dihedral
exceptions in JT 1.3; no elementary-rank bound is needed. -/
public theorem not_small_dihedral_of_sixteen
    {P : Type*} [Group P] [Finite P]
    (B : Subgroup P) (hB : Nat.card B = 16)
    (n : ℕ) (hn : n ≤ 4) : ¬ Nonempty (P ≃* DihedralGroup n) := by
  rintro ⟨e⟩
  have hle := B.card_le_card_group
  have hc : Nat.card P = 2 * n :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  omega

/-- The certified unitary model count transports through any multiplicative
equivalence, without a centrality or rank hypothesis. -/
public theorem card_involutions_eq_three_of_unitary
    {P : Type*} [Group P] (e : P ≃* UnitarySylow) :
    Nat.card {x : P // orderOf x = 2} = 3 := by
  let eI : {x : P // orderOf x = 2} ≃ {x : UnitarySylow // orderOf x = 2} :=
    Equiv.subtypeEquiv e.toEquiv (fun x => by
      change orderOf x = 2 ↔ orderOf (e x) = 2
      rw [e.orderOf_eq])
  exact (Nat.card_congr eI).trans unitarySylow_involution_count

/-- Assemble JT 1.3 and the centralizer consequence of JT 1.5. The latter
is needed only in the Hall–Janko branch. -/
public theorem outer_alternatives_of_sylow_models
    {G : Type*} [Group G] (S : Sylow 2 G)
    (hmodels : Nonempty (S ≃* HallJankoSylow) ∨ Nonempty (S ≃* UnitarySylow))
    (hHall : Nonempty (S ≃* HallJankoSylow) →
      ∃ z : G, orderOf z = 2 ∧ ¬ Group.IsSolvable (centralizer ({z} : Set G))) :
    Nat.card {x : S // orderOf x = 2} ≤ 3 ∨
      ∃ z : G, orderOf z = 2 ∧ ¬ Group.IsSolvable (centralizer ({z} : Set G)) := by
  rcases hmodels with h | h
  · exact Or.inr (hHall h)
  · obtain ⟨e⟩ := h
    exact Or.inl (card_involutions_eq_three_of_unitary e).le

/-- The JT 1.3/1.5 alternative in the marked central-two N₂ configuration.
The Hall–Janko case is excluded by its intrinsic radical fusion calculation;
the unitary case has exactly three involutions. -/
public theorem outer_alternatives_of_central_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (S : Sylow 2 G)
    (hnorm : normalizer (S : Set G) ≠
      (S : Subgroup G) ⊔ centralizer (S : Set G))
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧
      8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    [(NormalFourCentralOmegaTwo.fourImage S W).Normal]
    (hfused : ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 →
      orderOf v = 2 → IsConj (u : G) (v : G))
    (B : Subgroup S) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    Nat.card {x : S // orderOf x = 2} ≤ 3 ∨
      ∃ z : G, orderOf z = 2 ∧ ¬ Group.IsSolvable (centralizer ({z} : Set G)) := by
  apply outer_alternatives_of_sylow_models S
    (NormalEightExoticSylowModels.models_of_central_two
      hns hN S hnorm hZ hno W hW hunique hfused B hB)
  intro hmodel
  exact (HallJankoTrivialSylowAutomizer.false_of_marked_hallJanko
    hns hN S hmodel hZ hno W hW hunique hfused B hB).elim

end Stellmacher.Recognition.NormalEightExoticRecognition
