module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.MainConverse.Transport
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.LinearThreeFour.LinearThreeEven
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.LinearThreeFour.LinearFourEven
public import CFSG.Quasithin.MainConverse.OddClassicalLocal.LinearThreeFour.LinearFourThreeRank
public import Theory.SpecificGroups.LinearCoefficientEquiv
public import Theory.SpecificGroups.PSL3Three.QuasithinRank
public import Theory.SpecificGroups.PSL4Three.QuasithinRank

/-!
# The odd linear groups in dimensions three and four

The actual field isomorphism to ZMod 3 transports the projective matrix
model in `ClassicalGroup.IsPSL`. The nonabelian unitriangular Sylow group
proves the three-rank bound for PSL₃(3), and its other odd primes follow
from the order. Subgroup monotonicity then gives QT.

For PSL₄(3), its order bounds the nondefining odd-prime ranks, and the
involution and four-group centralizer calculations bound the three-rank
in every actual two-local. The intrinsic two-core calculations establish
even characteristic in both dimensions. Transport gives both QT and E
for every group identified with either projective matrix model.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed pp.4 and 482.
-/

namespace CFSG.Quasithin.MainConverse

/-- Replace the field witness by ZMod 3 using entrywise coefficient transport. -/
public theorem psl_three_field_model {G : Type*} [Group G] {n : ℕ}
    (hG : ClassicalGroup.IsPSL G n 3) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 3)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hG
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 3 :=
    (ZMod.ringEquivOfPrime F Nat.prime_three
      (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF)⟩

/-- The PSL₃(3) model is strongly quasithin, hence all of its two-locals are. -/
public theorem psl3_three_stronglyQuasithin {G : Type*} [Group G] [Finite G]
    (hG : ClassicalGroup.IsPSL G 3 3) : IsStronglyQuasithin G := by
  obtain ⟨e⟩ := psl_three_field_model hG
  intro p hp ho
  rw [Theory.GroupTheory.primeRank_equiv p e]
  exact Matrix.PSL3Three.odd_primeRank_le_two hp ho

/-- The complete QT clause for the PSL₃(3) alternative. -/
public theorem psl3_three_quasithin {G : Type*} [Group G] [Finite G]
    (hG : ClassicalGroup.IsPSL G 3 3) : IsQuasithin G :=
  (psl3_three_stronglyQuasithin hG).quasithin

/-- Nondefining odd-prime ranks transport to every PSL₄(3) model. -/
public theorem psl4_three_odd_primeRank_le_two {G : Type*} [Group G] [Finite G]
    (hG : ClassicalGroup.IsPSL G 4 3) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (h3 : p ≠ 3) : primeRank p G ≤ 2 := by
  obtain ⟨e⟩ := psl_three_field_model hG
  rw [Theory.GroupTheory.primeRank_equiv p e]
  exact Matrix.PSL4Three.odd_primeRank_le_two_of_ne_three hp ho h3

/-- QT for PSL₄(3) reduces to its local three-rank bound.
The unconditional theorem below supplies this premise. -/
public theorem psl4_three_quasithin_of_twoLocal_three_rank
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSL G 4 3)
    (hthree : ∀ M : Subgroup G, IsTwoLocal M → primeRank 3 M ≤ 2) :
    IsQuasithin G := by
  apply isQuasithin_iff_twoLocal.mpr
  intro M hM p hp ho
  by_cases h3 : p = 3
  · subst p
    exact hthree M hM
  exact (Theory.GroupTheory.primeRank_le_of_injective p M.subtype
    M.subtype_injective).trans (psl4_three_odd_primeRank_le_two hG hp ho h3)

/-- The intrinsic PSL₃(3) two-core calculation transports to every field witness. -/
public theorem psl3_three_evenCharacteristic_of_isPSL
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSL G 3 3) :
    IsEvenCharacteristic G := by
  obtain ⟨e⟩ := psl_three_field_model hG
  exact evenCharacteristic_of_model_equiv e psl3_three_evenCharacteristic

/-- The intrinsic PSL₄(3) two-core calculation transports to every field witness. -/
public theorem psl4_three_evenCharacteristic_of_isPSL
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSL G 4 3) :
    IsEvenCharacteristic G := by
  obtain ⟨e⟩ := psl_three_field_model hG
  exact evenCharacteristic_of_model_equiv e psl4_three_evenCharacteristic

/-- Transport the defining-prime bound on actual two-locals of PSL₄(3). -/
public theorem psl4_three_twoLocal_three_rank_of_isPSL
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSL G 4 3)
    (M : Subgroup G) (hM : IsTwoLocal M) : primeRank 3 M ≤ 2 := by
  obtain ⟨e⟩ := psl_three_field_model hG
  rw [Theory.GroupTheory.primeRank_equiv 3
    (Subgroup.equivMapOfInjective M e.toMonoidHom e.injective)]
  exact psl4_three_twoLocal_three_rank (M.map e.toMonoidHom)
    (Theory.GroupTheory.isTwoLocal_map e hM)

/-- The complete QT clause for PSL₄(3), including the local defining-prime bound. -/
public theorem psl4_three_quasithin {G : Type*} [Group G] [Finite G]
    (hG : ClassicalGroup.IsPSL G 4 3) : IsQuasithin G :=
  psl4_three_quasithin_of_twoLocal_three_rank hG
    (psl4_three_twoLocal_three_rank_of_isPSL hG)

/-- The QT and E clauses of the PSL₃(3) alternative. -/
public theorem psl3_three_qt_and_evenCharacteristic_of_isPSL
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSL G 3 3) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨psl3_three_quasithin hG, psl3_three_evenCharacteristic_of_isPSL hG⟩

/-- The QT and E clauses of the PSL₄(3) alternative. -/
public theorem psl4_three_qt_and_evenCharacteristic_of_isPSL
    {G : Type*} [Group G] [Finite G] (hG : ClassicalGroup.IsPSL G 4 3) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨psl4_three_quasithin hG, psl4_three_evenCharacteristic_of_isPSL hG⟩

/-- The two linear dimension-three/four cases of source Theorem 0.1.2(4).
The concrete calculations need no additional simplicity or local hypotheses. -/
public theorem psl_three_four_qt_and_evenCharacteristic_of_isPSL
    {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : n = 3 ∨ n = 4)
    (hG : ClassicalGroup.IsPSL G n 3) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  rcases hn with rfl | rfl
  · exact psl3_three_qt_and_evenCharacteristic_of_isPSL hG
  · exact psl4_three_qt_and_evenCharacteristic_of_isPSL hG

end CFSG.Quasithin.MainConverse
