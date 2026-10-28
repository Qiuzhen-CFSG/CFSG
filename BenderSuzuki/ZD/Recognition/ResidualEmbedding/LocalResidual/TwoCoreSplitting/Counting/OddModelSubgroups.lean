module

public import Theory.GroupTheory.OddInvolutionNormalizer
public import Theory.SpecificGroups.ProjectiveLinear.EvenOddTori
public import Theory.SpecificGroups.Suzuki.OddTorusContainment
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.OddModelSubgroups.Arithmetic

/-!
# Odd subgroups in the Section 17 local models

The concrete torus theorems prove the odd-order clauses of GLS, Volume 4,
Chapter 4, Lemmas 3.7 and 3.8, and all clauses of Lemma 3.11 for both SU₃
and PSU₃. They are publicly reexported here, including cyclic torus orders,
involution actions, the literal relative normalizer quotient, and the
unitary centralizer and commutator calculations.

This module assembles their consequences in Chapter 2, Lemmas 17.3–17.5.
For an odd subgroup H normalized by an involution t, with N(H) ≤ H⟨t⟩,
the relative index c = [H : C_H(t)] cannot be congruent to 1 modulo q in
the Suzuki case. In the unitary cases, exclusion from the actual Borels
and c ≠ 1 give the same contradiction: divisibility forces c = q+1,
which the Sylow-three argument rules out. In PSL₂ the congruence selects
the full cyclic torus of order q+1, inverted by t.

The results also transport through actual multiplicative equivalences.
Normalizer control and centralizer index remain intrinsic to the source
carrier; the unitary no-Borel hypotheses concern its image in the actual
matrix model. The Section 17 counting consumer supplies these local
hypotheses from Lemma 17.2 and retains the final permutation-degree argument.
No ambient ZD assumption is used here.

Sources: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 17.3–17.5, and
`refs/KGroup/GLS4/Chapter4.tex`, Lemmas 3.7, 3.8, 3.11. Suzuki parameters
are the matrix-field order q = 2^(2m+1) and torus orders q−1,
q ± 2^(m+1) + 1, as in GLS, Volume 3, Theorem 6.5.4.
-/

namespace BenderSuzuki.ZD
open Subgroup BenderSuzuki.MatrixGroups
open UnitaryThree.OddTorusNormalizer

private theorem two_lt_binary {n : ℕ} (hn : 2 ≤ n) : 2 < (2 : ℕ) ^ n :=
  lt_of_lt_of_le (by decide : 2 < (2 : ℕ) ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)

/-- The linear model conclusion needed in GLS4, 2.17.5: H is a full
nonsplit torus and its fixed-point index is q+1. The subgroup and its
normalizer live in the original carrier of the given model isomorphism. -/
public theorem psl2_odd_normalizer_index_eq_succ_of_equiv
    {G E : Type*} [Group G] [Field E] [Finite E]
    {n : ℕ} (hcard : Nat.card E = 2 ^ n) (hn : 2 ≤ n)
    (e : G ≃* PSL2MatrixGroup E) (H : Subgroup G) (hodd : Odd (Nat.card H))
    {t : G} (ht : orderOf t = 2) (htH : t ∈ normalizer H)
    (hN : normalizer H ≤ H ⊔ zpowers t)
    (hc : (centralizer ({t} : Set G)).relIndex H ≠ 1)
    (hmod : (centralizer ({t} : Set G)).relIndex H % (2 ^ n) = 1) :
    IsCyclic H ∧ Nat.card H = 2 ^ n + 1 ∧
      (∀ x ∈ H, t * x * t⁻¹ = x⁻¹) ∧
      (centralizer ({t} : Set G)).relIndex H = 2 ^ n + 1 := by
  have hnc : ¬ H ≤ centralizer ({t} : Set G) := fun h => hc (relIndex_eq_one.mpr h)
  obtain ⟨hcyc, horders, hinv, hindex⟩ :=
    EvenOddTori.odd_normalizer_of_equiv hcard hn e H hodd ht htH hnc hN
  rw [hcard] at horders
  have horder := linear_torus_order_eq_succ (two_lt_binary hn) (hindex ▸ hmod) horders
  exact ⟨hcyc, horder, hinv, hindex.trans horder⟩

/-- Concrete PSL₂ form of the source's selection of the q+1 torus. -/
public theorem psl2_odd_normalizer_index_eq_succ
    {E : Type*} [Field E] [Finite E]
    {n : ℕ} (hcard : Nat.card E = 2 ^ n) (hn : 2 ≤ n)
    (H : Subgroup (PSL2MatrixGroup E)) (hodd : Odd (Nat.card H))
    {t : PSL2MatrixGroup E} (ht : orderOf t = 2) (htH : t ∈ normalizer H)
    (hN : normalizer H ≤ H ⊔ zpowers t)
    (hc : (centralizer ({t} : Set (PSL2MatrixGroup E))).relIndex H ≠ 1)
    (hmod : (centralizer ({t} : Set (PSL2MatrixGroup E))).relIndex H % (2 ^ n) = 1) :
    IsCyclic H ∧ Nat.card H = 2 ^ n + 1 ∧
      (∀ x ∈ H, t * x * t⁻¹ = x⁻¹) ∧
      (centralizer ({t} : Set (PSL2MatrixGroup E))).relIndex H = 2 ^ n + 1 :=
  psl2_odd_normalizer_index_eq_succ_of_equiv hcard hn (MulEquiv.refl _)
    H hodd ht htH hN hc hmod

/-- The Suzuki contradiction of GLS4, 2.17.3, using the matrix-field
order q=2^(2m+1). No noncentrality premise is needed for this stronger form. -/
public theorem suzuki_odd_normalizer_index_not_congruent_one
    {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) (hodd : Odd (Nat.card H))
    {t : SuzukiMatrixGroup m} (ht : orderOf t = 2) (htH : t ∈ normalizer H)
    (hN : normalizer H ≤ H ⊔ zpowers t) :
    (centralizer ({t} : Set (SuzukiMatrixGroup m))).relIndex H % (2 ^ (2 * m + 1)) ≠ 1 := by
  obtain ⟨hindex, horders⟩ := suzukiOddSubgroup_centralizer_index hm H hodd ht htH hN
  rw [hindex]
  exact suzuki_torus_order_not_congruent_one m (Nat.card H) hm horders

/-- The SU₃ contradiction of GLS4, 2.17.4. The field of matrices has
order q²; its Hermitian fixed field has order q=2^n. -/
public theorem special_unitary_odd_normalizer_index_not_congruent_one
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H))
    (t : J.specialSubgroup) (ht : orderOf t = 2) (htH : t ∈ normalizer H)
    (hB : SpecialNoBorel J H) (hN : normalizer H ≤ H ⊔ zpowers t)
    (hc : (centralizer ({t} : Set J.specialSubgroup)).relIndex H ≠ 1) :
    (centralizer ({t} : Set J.specialSubgroup)).relIndex H % (2 ^ n) ≠ 1 := by
  obtain ⟨_, _, _, hdvd, hne⟩ :=
    special_odd_subgroup_constraints J hn hcard hfixed H hodd t ht htH hB hN
  intro hmod
  exact hne (unitary_index_eq_succ_of_dvd (two_lt_binary hn) hc hmod hdvd)

/-- The PSU₃ contradiction of GLS4, 2.17.4. The invoked torus theorem
retains the scalar divisor gcd(3,q+1) in its second cyclic factor. -/
public theorem projective_unitary_odd_normalizer_index_not_congruent_one
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hodd : Odd (Nat.card H))
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (htH : t ∈ normalizer H) (hB : ProjectiveNoBorel J H)
    (hN : normalizer H ≤ H ⊔ zpowers t)
    (hc : (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))).relIndex H ≠ 1) :
    (centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))).relIndex H % (2 ^ n) ≠ 1 := by
  obtain ⟨_, _, _, hdvd, hne⟩ :=
    projective_odd_subgroup_constraints J hn hcard hfixed H hodd t ht htH hB hN
  intro hmod
  exact hne (unitary_index_eq_succ_of_dvd (two_lt_binary hn) hc hmod hdvd)

section Transport
variable {G K : Type*} [Group G] [Group K]

private theorem centralizer_index_map (e : G ≃* K) (H : Subgroup G) (t : G) :
    (centralizer ({e t} : Set K)).relIndex (H.map e.toMonoidHom) =
      (centralizer ({t} : Set G)).relIndex H := by
  have he : (centralizer ({e t} : Set K)).comap e.toMonoidHom =
      centralizer ({t} : Set G) := by
    ext x
    simp only [mem_comap, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      ← map_mul, e.injective.eq_iff]
  rw [← relIndex_comap, he]

private theorem normalizer_bound_map (e : G ≃* K) (H : Subgroup G) (t : G)
    (hN : normalizer H ≤ H ⊔ zpowers t) :
    normalizer (H.map e.toMonoidHom) ≤ H.map e.toMonoidHom ⊔ zpowers (e t) := by
  simpa only [map_equiv_normalizer_eq, Subgroup.map_sup, MonoidHom.map_zpowers,
    MulEquiv.coe_toMonoidHom] using (map_mono (f := e.toMonoidHom) hN)

/-- Transport of the Suzuki exclusion through an actual model equivalence,
with the index and normalizer hypotheses in the original carrier. -/
public theorem suzuki_odd_normalizer_index_not_congruent_one_of_equiv
    {m : ℕ} (hm : 0 < m) (e : G ≃* SuzukiMatrixGroup m)
    (H : Subgroup G) (hodd : Odd (Nat.card H))
    {t : G} (ht : orderOf t = 2) (htH : t ∈ normalizer H)
    (hN : normalizer H ≤ H ⊔ zpowers t) :
    (centralizer ({t} : Set G)).relIndex H % (2 ^ (2 * m + 1)) ≠ 1 := by
  have ho : Odd (Nat.card (H.map e.toMonoidHom)) := by
    simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective] using hodd
  have ht' : orderOf (e t) = 2 := (e.orderOf_eq t).trans ht
  have htH' : e t ∈ normalizer (H.map e.toMonoidHom) :=
    le_normalizer_map e.toMonoidHom (mem_map_of_mem _ htH)
  have h := suzuki_odd_normalizer_index_not_congruent_one hm
    (H.map e.toMonoidHom) ho ht' htH' (normalizer_bound_map e H t hN)
  rwa [centralizer_index_map] at h

/-- Transport of the SU₃ exclusion. The no-Borel hypothesis is stated on
the image of H under the actual equivalence to the special-unitary carrier. -/
public theorem special_unitary_odd_normalizer_index_not_congruent_one_of_equiv
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (e : G ≃* J.specialSubgroup) (H : Subgroup G) (hodd : Odd (Nat.card H))
    (t : G) (ht : orderOf t = 2) (htH : t ∈ normalizer H)
    (hB : SpecialNoBorel J (H.map e.toMonoidHom))
    (hN : normalizer H ≤ H ⊔ zpowers t)
    (hc : (centralizer ({t} : Set G)).relIndex H ≠ 1) :
    (centralizer ({t} : Set G)).relIndex H % (2 ^ n) ≠ 1 := by
  have ho : Odd (Nat.card (H.map e.toMonoidHom)) := by
    simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective] using hodd
  have ht' : orderOf (e t) = 2 := (e.orderOf_eq t).trans ht
  have htH' : e t ∈ normalizer (H.map e.toMonoidHom) :=
    le_normalizer_map e.toMonoidHom (mem_map_of_mem _ htH)
  have hc' : (centralizer ({e t} : Set J.specialSubgroup)).relIndex
      (H.map e.toMonoidHom) ≠ 1 := by rwa [centralizer_index_map]
  have h := special_unitary_odd_normalizer_index_not_congruent_one J hn hcard hfixed
    (H.map e.toMonoidHom) ho (e t) ht' htH' hB (normalizer_bound_map e H t hN) hc'
  rwa [centralizer_index_map] at h

/-- Transport of the PSU₃ exclusion through the actual projective carrier,
retaining the geometric no-Borel condition on the image of H. -/
public theorem projective_unitary_odd_normalizer_index_not_congruent_one_of_equiv
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (H : Subgroup G) (hodd : Odd (Nat.card H))
    (t : G) (ht : orderOf t = 2) (htH : t ∈ normalizer H)
    (hB : ProjectiveNoBorel J (H.map e.toMonoidHom))
    (hN : normalizer H ≤ H ⊔ zpowers t)
    (hc : (centralizer ({t} : Set G)).relIndex H ≠ 1) :
    (centralizer ({t} : Set G)).relIndex H % (2 ^ n) ≠ 1 := by
  have ho : Odd (Nat.card (H.map e.toMonoidHom)) := by
    simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective] using hodd
  have ht' : orderOf (e t) = 2 := (e.orderOf_eq t).trans ht
  have htH' : e t ∈ normalizer (H.map e.toMonoidHom) :=
    le_normalizer_map e.toMonoidHom (mem_map_of_mem _ htH)
  have hc' : (centralizer ({e t} : Set (ProjectiveSpecialUnitaryMatrixGroup J))).relIndex
      (H.map e.toMonoidHom) ≠ 1 := by rwa [centralizer_index_map]
  have h := projective_unitary_odd_normalizer_index_not_congruent_one J hn hcard hfixed
    (H.map e.toMonoidHom) ho (e t) ht' htH' hB (normalizer_bound_map e H t hN) hc'
  rwa [centralizer_index_map] at h

end Transport
end BenderSuzuki.ZD
