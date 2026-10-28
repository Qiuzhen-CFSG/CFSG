module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Definitions
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.PureActors
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Transport
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.RepresentativeImages.InnerImages.Coordinates
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.SelfNormalizingSylowOvergroups
public import Theory.GroupTheory.TwoThreeSolvable


/-!
# Solvable Sylow overgroups in automorphism extensions of Held

The literal pure pair product has order 9216 and is self-normalizing, since
it contains a self-normalizing Held Sylow two-subgroup. Its certified outer
quarter-turn and the proved permutation-normalizer bound give its full
normalizer in Aut(He) order 18432, assuming automorphism realization.
Comparison with the inner Sylow index shows that this normalizer has odd index.

Sylow conjugacy puts any two-subgroup into a conjugate of this normalizer.
Intersect with the specified ambient group containing Inn(He). This retains
the conjugated inner product of order 9216, so nine still divides the order.
The intersection's order divides 18432 = 2^11 * 3^2; the proved two-and-three
specialization of Burnside's theorem establishes its solvability.

Sources: Aschbacher--Smith E.1.14(4), refs/quasithin.pdf, printed p.214;
GLS3 Table 5.3p; ATLAS Hed2G1-max8W1. The normalizer and outer-actor arguments
adapt the existing ProperExtensionProfile/Quotients/{NormalizerReduction,
InnerNormalizers,PureActor} proofs, using only their lower Theory inputs.
No simplicity, maximal-subgroup classification or E-generation premise is used.
-/

open Subgroup
open Held.LocalPairs Held.LocalPairs.PairCoverage.LocalActions
open Held.LocalPairs.SylowGeometry.Calculations
open RepresentativeImages
namespace Held.RankOneLocalPair
namespace Solvable

private abbrev innerLocal : Subgroup He := Exhaustion.candidateProduct false 0
private abbrev candidate : Subgroup (MulAut He) := automorphismNormalizer innerLocal

private theorem exists_inner_sylow : ∃ T : Sylow 2 He, (T : Subgroup He) = candidateTwo false 0 := by
  obtain ⟨P, hP⟩ := exists_representative_sylow representative_isPGroup InnerNormalizer.normalizer_eq
  refine ⟨P.mapSurjective (f := (MulAut.conj (InnerImages.transporter false 0)).toMonoidHom)
    (MulAut.conj _).surjective, ?_⟩
  change (P : Subgroup He).map _ = _
  rw [hP]
  exact InnerImages.representative_map false 0

private theorem innerLocal_self_normalizing : normalizer (innerLocal : Set He) = innerLocal := by
  obtain ⟨T, hT⟩ := exists_inner_sylow
  apply normalizer_eq_of_self_normalizing_sylow T (inner_self_normalizing T)
  rw [hT]
  exact le_sup_right

/-- The inner part of a self-normalizing subgroup's full automorphism normalizer. -/
private noncomputable def normalizerInnerEquiv (U : Subgroup Held.He)
    (hU : normalizer (U : Set Held.He) = U) :
    U ≃* (MulAut.innerSubgroup Held.He).subgroupOf (automorphismNormalizer U) := by
  let f : U →* (MulAut.innerSubgroup Held.He).subgroupOf (automorphismNormalizer U) :=
    { toFun := fun x => ⟨⟨MulAut.conj x.val,
        mem_normalizer_iff_map_conj_eq.mp (U.le_normalizer x.property)⟩, ⟨x.val, rfl⟩⟩
      map_one' := by ext : 2; exact map_one (MulAut.conj : Held.He →* MulAut Held.He)
      map_mul' := fun x y => by ext : 2; exact map_mul (MulAut.conj : Held.He →* MulAut Held.He) x.val y.val }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    exact Theory.GroupTheory.conj_injective_of_center_eq_bot Held.LocalPairs.center_eq_bot
      (congrArg (fun a => a.val.val) h)
  · intro a
    obtain ⟨x, hx⟩ := a.property
    have hn : x ∈ normalizer (U : Set Held.He) :=
      mem_normalizer_iff_map_conj_eq.mpr (hx ▸ a.val.property)
    exact ⟨⟨x, hU ▸ hn⟩, Subtype.ext (Subtype.ext hx)⟩

/-- The realized permutation-normalizer bound controls the full outer index. -/
private theorem outer_index_le_two
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom) :
    (MulAut.innerSubgroup Held.He).index ≤ 2 :=
  (Nat.card_le_card_of_surjective _
    (normalizerOuterAction_surjective Held.permutationGroup hreal)).trans Held.permutationNormalizerQuotient_card_le_two

/-- Every automorphism normalizer has inner index dividing two. -/
private theorem normalizer_inner_index_dvd_two (U : Subgroup Held.He)
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom) :
    ((MulAut.innerSubgroup Held.He).subgroupOf (automorphismNormalizer U)).index ∣ 2 := by
  have hd := relIndex_dvd_index_of_normal (MulAut.innerSubgroup Held.He)
    (automorphismNormalizer U)
  have hi := outer_index_le_two hreal
  have hp := Nat.pos_of_ne_zero (MulAut.innerSubgroup Held.He).index_ne_zero_of_finite
  have h12 : (MulAut.innerSubgroup Held.He).index = 1 ∨
      (MulAut.innerSubgroup Held.He).index = 2 := by omega
  exact hd.trans (h12.elim (fun h => h ▸ one_dvd _) (fun h => h ▸ dvd_rfl))

/-- The already certified pure-pair outer actor in the full automorphism group. -/
private def pureAutomorphism : MulAut Held.He :=
  Held.permutationGroup.normalizerMonoidHom (PureActors.actor false).val

/-- The actor preserves both factors and hence their literal join. -/
private theorem pureAutomorphism_mem : pureAutomorphism ∈ candidate := by
  change (candidateOdd false 0 ⊔ candidateTwo false 0).map pureAutomorphism.toMonoidHom =
    candidateOdd false 0 ⊔ candidateTwo false 0
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (PureActors.actor false).property.2
    (PureActors.actor false).property.1

/-- Inner pair actors preserve the two marked axes; the quarter-turn does not. -/
private theorem pureAutomorphism_not_inner : pureAutomorphism ∉ MulAut.innerSubgroup Held.He := by
  rintro ⟨x, hx⟩
  have hn : x ∈ normalizer (candidateTwo false 0 : Set Held.He) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hx]
    exact (PureActors.actor false).property.1
  have hxS : x ∈ candidateTwo false 0 := by
    rwa [InnerImages.candidateTwo_normalizer InnerNormalizer.normalizer_eq false 0] at hn
  apply PureActors.coordinateAction_not_mem_diagonal false
  apply InnerImages.mem_diagonal_of_vectors
  intro k
  apply InnerImages.coordinates_of_conjugation false 0 k x hxS
  rw [InnerImages.markedEmbedding_eq, PureActors.candidateOddEquiv_symm_image]
  apply Held.representation_injective
  rw [← PureActors.actor_conj_basis]
  have he := MulEquiv.congr_fun hx (basisGenerator false 0 k)
  exact (congrArg Held.representation he).symm

/-- The explicit outer actor makes the inner index exactly two. -/
private theorem candidate_inner_index
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom) :
    ((MulAut.innerSubgroup Held.He).subgroupOf candidate).index = 2 := by
  let I := (MulAut.innerSubgroup Held.He).subgroupOf candidate
  have hp : I ≠ ⊤ := by
    intro he
    have hm : (⟨pureAutomorphism, pureAutomorphism_mem⟩ : candidate) ∈ I :=
      he ▸ Subgroup.mem_top _
    exact pureAutomorphism_not_inner hm
  have h1 := I.one_lt_index_of_ne_top hp
  have h2 := Nat.le_of_dvd (by decide : 0 < 2) (normalizer_inner_index_dvd_two innerLocal hreal)
  change I.index ≤ 2 at h2
  exact Nat.le_antisymm h2 h1

/-- The full automorphism normalizer of the pure pair product has order 18432. -/
private theorem candidate_card
    (hreal : Function.Surjective Held.permutationGroup.normalizerMonoidHom) :
    Nat.card candidate = 18432 := by
  let I := (MulAut.innerSubgroup Held.He).subgroupOf candidate
  have he := Nat.card_congr (normalizerInnerEquiv innerLocal innerLocal_self_normalizing).toEquiv
  change Nat.card innerLocal = Nat.card I at he
  rw [← I.card_mul_index, candidate_inner_index hreal, ← he]
  change Nat.card (Exhaustion.candidateProduct false 0) * 2 = 18432
  rw [(Exhaustion.candidateOrders false 0).2.2]



private theorem outer_index_two
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom) :
    (MulAut.innerSubgroup He).index = 2 := by
  have hn : MulAut.innerSubgroup He ≠ ⊤ := by
    intro he
    exact pureAutomorphism_not_inner (he ▸ mem_top _)
  have h := (MulAut.innerSubgroup He).one_lt_index_of_ne_top hn
  exact Nat.le_antisymm (outer_index_le_two hreal) h

private theorem candidate_odd_index
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom) :
    ¬ 2 ∣ candidate.index := by
  obtain ⟨T, hT⟩ := exists_inner_sylow
  have hcT : Nat.card T = 1024 := by
    rw [hT]
    exact (Exhaustion.candidateOrders false 0).1
  have hcI : Nat.card (MulAut.innerSubgroup He) = Nat.card He :=
    (Nat.card_congr (MonoidHom.ofInjective
      (Theory.GroupTheory.conj_injective_of_center_eq_bot Held.LocalPairs.center_eq_bot)).toEquiv).symm
  have ht := T.toSubgroup.card_mul_index
  have hi := (MulAut.innerSubgroup He).card_mul_index
  have hn := candidate.card_mul_index
  rw [hcT] at ht
  rw [hcI, outer_index_two hreal] at hi
  rw [candidate_card hreal] at hn
  have he : 9 * candidate.index = T.toSubgroup.index := by omega
  intro h
  apply T.not_dvd_index
  rw [← he]
  exact dvd_mul_of_dvd_right h _

private theorem candidate_inner_le : innerLocal.map (MulAut.conj : He →* MulAut He) ≤ candidate := by
  rintro _ ⟨x, hx, rfl⟩
  exact mem_normalizer_iff_map_conj_eq.mp (innerLocal.le_normalizer hx)

private theorem prime_dvd_18432 {p : ℕ} (hp : p.Prime) (hd : p ∣ 18432) :
    p = 2 ∨ p = 3 := by
  have he : 18432 = 2 ^ 11 * 3 ^ 2 := by norm_num
  rw [he] at hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)

private theorem overgroup
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom)
    (A : Subgroup (MulAut He)) (hA : MulAut.innerSubgroup He ≤ A)
    (S : Sylow 2 A) :
    ∃ B : Subgroup A, (S : Subgroup A) ≤ B ∧ 9 ∣ Nat.card B ∧ Group.IsSolvable B := by
  classical
  let Q : Sylow 2 candidate := Classical.choice inferInstance
  have hindex : ¬ 2 ∣ ((Q : Subgroup candidate).map candidate.subtype).index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul Q.not_dvd_index (candidate_odd_index hreal)
  let P : Sylow 2 (MulAut He) := (Q.isPGroup'.map candidate.subtype).toSylow hindex
  have hP : (P : Subgroup (MulAut He)) ≤ candidate := map_subtype_le _
  obtain ⟨R, hSR⟩ := (S.isPGroup'.map A.subtype).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut He) P R
  let f := (MulAut.conj g).toMonoidHom
  let H := candidate.map f
  have hSH : (S : Subgroup A).map A.subtype ≤ H := by
    apply hSR.trans
    rw [← hg]
    exact map_mono hP
  let B := H.subgroupOf A
  have hSB : (S : Subgroup A) ≤ B := by
    intro x hx
    exact hSH (mem_map.mpr ⟨x, hx, rfl⟩)
  have hBH : Nat.card B ∣ Nat.card H := card_comap_dvd_of_injective H A.subtype A.subtype_injective
  have hHcard : Nat.card H = 18432 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact candidate_card hreal
  have hsol : Group.IsSolvable B :=
    Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three B (fun p hp hd =>
      prime_dvd_18432 hp (hd.trans (hHcard ▸ hBH)))
  let J := innerLocal.map (MulAut.conj : He →* MulAut He)
  let W := J.map f
  have hWH : W ≤ H := map_mono candidate_inner_le
  have hWI : W ≤ MulAut.innerSubgroup He := by
    rintro _ ⟨x, hx, rfl⟩
    exact (inferInstance : (MulAut.innerSubgroup He).Normal).conj_mem x ((map_le_range (MulAut.conj : He →* MulAut He) innerLocal) hx) g
  have hWA : W ≤ A := hWI.trans hA
  have hWcard : Nat.card W = 9216 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    rw [card_map_of_injective (Theory.GroupTheory.conj_injective_of_center_eq_bot Held.LocalPairs.center_eq_bot)]
    exact (Exhaustion.candidateOrders false 0).2.2
  have hWAc : Nat.card (W.subgroupOf A) = 9216 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWA).toEquiv).trans hWcard
  have hWB : W.subgroupOf A ≤ B := fun _ hx => hWH hx
  refine ⟨B, hSB, ?_, hsol⟩
  exact (show 9 ∣ Nat.card (W.subgroupOf A) by rw [hWAc]; norm_num).trans (card_dvd_of_le hWB)

end Solvable

/-- Every specified automorphism overgroup of Held has a solvable Sylow overgroup
whose order is divisible by nine. Automorphism realization is the only premise. -/
public theorem solvableOvergroups_of_realization
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom) :
    SolvableOvergroups := by
  intro A hA S _
  exact Solvable.overgroup hreal A hA S

end Held.RankOneLocalPair
