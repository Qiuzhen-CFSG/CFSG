module

public import CFSG.Quasithin.ClassificationModels.Families
public import CFSG.Quasithin.MainConverse.SporadicLocal.Criteria
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Janko4.Model.OddLocalRanks
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Reduction
public import CFSG.Quasithin.MainConverse.SporadicLocal.J4.EvenCharacteristic
public import CFSG.Quasithin.MainConverse.SporadicLocal.J4.SylowCenterEven

/-!
# Quasithinness and even characteristic of J₄

The actual order-27 and order-1331 word subgroups are nonabelian by the
kernel-checked matrix certificates. The proved exact ambient order makes
their indices prime to 3 and 11, respectively, making them Sylow.
The other odd prime cubes do not divide that order. Hence the whole model
has odd prime rank at most two, which implies QT for each of its two-locals.
All generator-relation inputs are discharged by the matrix certificates.

For E, the full centralizer of the certified involution has a self-centralizing
two-core with center of order two. The imported Sylow-center argument promotes
its Sylow two-subgroup to the ambient group and applies the local centralizer
criterion to every two-local containing it.

Together these prove QT and E across an actual multiplicative equivalence
to `ClassificationModels.SporadicName.j4.Carrier`, definitionally `Janko4.Model`.
The conclusion needs no additional order, local-cover, simplicity,
nonabelianness or proper-K premise. The earlier order-bound and
maximal-Sylow-overgroup reductions remain available as conditional results.

Sources: Aschbacher–Smith, Theorem 0.1.2(5), printed p.4, repeated as
Theorem 0.1.1(5), printed p.482; GLS, Number 3, Table 5.3i, printed p.270,
with source order `2^21 * 3^3 * 5 * 7 * 11^3 * 23 * 29 * 31 * 37 * 43`.
-/

public section

namespace CFSG.Quasithin.MainConverse.SporadicLocal
open Subgroup Janko4 Janko4.Simplicity

private theorem j4_odd_cube_not_dvd {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (h3 : p ≠ 3) (h11 : p ≠ 11) : ¬ p ^ 3 ∣ 86775571046077562880 := by
  intro hd
  have hpd := prime_dvd_model_order hp ((dvd_pow_self p (by decide : 3 ≠ 0)).trans hd)
  rcases hpd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ho.not_two_dvd_nat (dvd_refl 2)
  · exact h3 rfl
  · norm_num at hd
  · norm_num at hd
  · exact h11 rfl
  · norm_num at hd
  · norm_num at hd
  · norm_num at hd
  · norm_num at hd
  · norm_num at hd

/-- The certified order-27 word subgroup is Sylow under the ambient order bound. -/
theorem j4_exists_nonabelian_sylow_three_of_card_dvd
    (hcard : Nat.card Model ∣ 86775571046077562880) :
    ∃ P : Sylow 3 Model, Nat.card P = 3 ^ 3 ∧ ¬ IsMulCommutative P := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let H := threeLocalSubgroup matrixA_mul_self matrixB_pow_four
  have hc : Nat.card H = 3 ^ 3 := threeLocal_card _ _
  have hi : ¬ 3 ∣ H.index := by
    intro hi
    have hd : 3 ^ 4 ∣ Nat.card Model := by
      rw [← H.card_mul_index, hc]
      exact Nat.mul_dvd_mul_left (3 ^ 3) hi
    have hb := hd.trans hcard
    norm_num at hb
  exact ⟨(IsPGroup.of_card hc).toSylow hi, hc,
    threeLocal_not_isMulCommutative _ _⟩

/-- The certified order-1331 word subgroup is Sylow under the ambient order bound. -/
theorem j4_exists_nonabelian_sylow_eleven_of_card_dvd
    (hcard : Nat.card Model ∣ 86775571046077562880) :
    ∃ P : Sylow 11 Model, Nat.card P = 11 ^ 3 ∧ ¬ IsMulCommutative P := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let H := Elevens.localSubgroup matrixA_mul_self matrixB_pow_four
  have hc : Nat.card H = 11 ^ 3 := Elevens.local_card _ _
  have hi : ¬ 11 ∣ H.index := by
    intro hi
    have hd : 11 ^ 4 ∣ Nat.card Model := by
      rw [← H.card_mul_index, hc]
      exact Nat.mul_dvd_mul_left (11 ^ 3) hi
    have hb := hd.trans hcard
    norm_num at hb
  exact ⟨(IsPGroup.of_card hc).toSylow hi, hc,
    Elevens.local_not_isMulCommutative _ _⟩

/-- The ambient order bound discharges all odd-rank cases, including 3 and 11. -/
theorem j4_stronglyQuasithin_of_card_dvd
    (hcard : Nat.card Model ∣ 86775571046077562880) :
    IsStronglyQuasithin Model := by
  apply stronglyQuasithin_of_odd_sylow_cases
  intro p hp ho
  by_cases h3 : p = 3
  · subst p
    exact Or.inr (j4_exists_nonabelian_sylow_three_of_card_dvd hcard)
  by_cases h11 : p = 11
  · subst p
    exact Or.inr (j4_exists_nonabelian_sylow_eleven_of_card_dvd hcard)
  exact Or.inl (fun hd => j4_odd_cube_not_dvd hp ho h3 h11 (hd.trans hcard))

/-- Transport QT across an actual equivalence with the fixed binary-matrix carrier. -/
theorem j4_quasithin_of_equiv_of_card_dvd
    {G : Type*} [Group G] [Finite G] (e : G ≃* Model)
    (hcard : Nat.card Model ∣ 86775571046077562880) : IsQuasithin G := by
  have hG : IsStronglyQuasithin G := by
    intro p hp ho
    exact (Theory.GroupTheory.primeRank_le_of_injective p e.toMonoidHom e.injective).trans
      (j4_stronglyQuasithin_of_card_dvd hcard p hp ho)
  exact hG.quasithin

/-- The exact matrix-group order discharges every odd-prime rank bound. -/
theorem j4_stronglyQuasithin :
    IsStronglyQuasithin ClassificationModels.SporadicName.j4.Carrier :=
  j4_stronglyQuasithin_of_card_dvd Cardinality.model_card.dvd

/-- Quasithinness transports across the actual J₄ catalogue equivalence. -/
theorem j4_quasithin_of_equiv
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* ClassificationModels.SporadicName.j4.Carrier) : IsQuasithin G :=
  j4_quasithin_of_equiv_of_card_dvd e Cardinality.model_card.dvd

/-- Even characteristic of the unchanged binary-matrix J₄ carrier. -/
theorem j4_evenCharacteristic :
    IsEvenCharacteristic ClassificationModels.SporadicName.j4.Carrier :=
  J4SylowCenterEven.evenCharacteristic

/-- The J₄ converse: QT and E across the actual catalogue equivalence.
All concrete order and local-structure premises have been discharged. -/
theorem j4_qt_e_of_equiv
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* ClassificationModels.SporadicName.j4.Carrier) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨j4_quasithin_of_equiv e, J4SylowCenterEven.evenCharacteristic_of_equiv e⟩

open Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- Conditional J₄ assembly, retaining the three remaining model obligations.
Every equivalence is to an actual carrier, and simplicity comes from G. -/
theorem j4_qt_and_even_of_order_bound_and_maximal_sylow_cover
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (e : G ≃* Model)
    (hcard : Nat.card Model ∣ 86775571046077562880)
    (hc4 : HasCharacteristicTwo max4Subgroup)
    (hcover : ∀ (T : Sylow 2 Model) (L : Subgroup Model), IsCoatom L →
      (T : Subgroup Model) ≤ L →
      Nonempty (L ≃* Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four) ∨
        Nonempty (L ≃* sourceSubgroup) ∨ Nonempty (L ≃* max4Subgroup)) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  let : IsSimpleGroup Model := e.symm.isSimpleGroup
  have hnaM : ¬ IsMulCommutative Model := by
    intro hc
    apply hna
    refine isMulCommutative_iff.mpr ?_
    intro x y
    apply e.injective
    simpa only [map_mul] using (isMulCommutative_iff.mp hc (e x) (e y))
  exact ⟨j4_quasithin_of_equiv_of_card_dvd e hcard,
    evenCharacteristic_of_model_equiv e
      (j4_evenCharacteristic_of_maximal_sylow_cover hnaM hc4 hcover)⟩

end CFSG.Quasithin.MainConverse.SporadicLocal
