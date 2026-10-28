module
public import Theory.GroupTheory.Recognition.Brauer.PlaneData
public import Theory.GroupTheory.ConjugateCosetStabilizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The total number of Brauer point and line blocks

For Brauer's first three postulates, the number of actual points and the
number of actual lines both equal the index of `M C(j)`, represented by
`M ⊔ C(j)`. This is equation (2.7) and the total-count assertion in (2E) of
Brauer, *On finite Desarguesian planes I*, article p. 120. It transfers the
later postulate (IV) to an upper bound for the actual geometry.

The generic conjugate-coset stabilizer calculation identifies each family
size with the index of its own subgroup join. Normalization and trivial
intersection express each join order as a product with `|C(j)|`. Postulate
(IIa), `|M| = |Mstar|`, equates these orders. The finite index formula then
equates the two indices. No projective-plane property or final count
`q² + q + 1` is used.
-/

open scoped Pointwise
namespace Theory.GroupTheory.BrauerPlaneSeed
/-- Brauer I (2.7), (2E): both block families have the same source index. -/
public theorem block_card_eq_index {G : Type*} [Group G] [Finite G] (S : BrauerPlaneSeed G)
    :
    Nat.card S.Point = (S.M ⊔ Subgroup.centralizer ({S.j} : Set G)).index ∧
    Nat.card S.Line = (S.M ⊔ Subgroup.centralizer ({S.j} : Set G)).index := by
  have hjoin : Nat.card ↥(S.M ⊔ Subgroup.centralizer ({S.j} : Set G)) =
      Nat.card ↥(S.Mstar ⊔ Subgroup.centralizer ({S.j} : Set G)) := by
    rw [Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint S.M _
        S.centralizer_le_normalizer_M S.disjoint_M_centralizer,
      Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint S.Mstar _
        S.centralizer_le_normalizer_Mstar S.disjoint_Mstar_centralizer,
      S.card_M_eq_Mstar]
  have hp : Nat.card S.Point = (S.M ⊔ Subgroup.centralizer ({S.j} : Set G)).index := by
    change Nat.card ↥(MulAction.orbit (ConjAct G) (S.j • (S.M : Set G))) = _
    rw [Nat.card_coe_set_eq]
    exact ncard_conjugate_coset_orbit_eq_index S.M S.j
      S.centralizer_le_normalizer_M S.disjoint_M_centralizer
  have hl : Nat.card S.Line = (S.Mstar ⊔ Subgroup.centralizer ({S.j} : Set G)).index := by
    change Nat.card ↥(MulAction.orbit (ConjAct G) (S.j • (S.Mstar : Set G))) = _
    rw [Nat.card_coe_set_eq]
    exact ncard_conjugate_coset_orbit_eq_index S.Mstar S.j
      S.centralizer_le_normalizer_Mstar S.disjoint_Mstar_centralizer
  have hindex : (S.Mstar ⊔ Subgroup.centralizer ({S.j} : Set G)).index =
      (S.M ⊔ Subgroup.centralizer ({S.j} : Set G)).index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(S.M ⊔ Subgroup.centralizer ({S.j} : Set G))))
    rw [hjoin]
    exact (S.Mstar ⊔ Subgroup.centralizer ({S.j} : Set G)).card_mul_index.trans
      (by rw [← hjoin]; exact (S.M ⊔ Subgroup.centralizer ({S.j} : Set G)).card_mul_index.symm)
  exact ⟨hp, hl.trans hindex⟩
end Theory.GroupTheory.BrauerPlaneSeed
