module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Orders.Pure

/-!
# The other two ambient centralizer orders

A singular diagonal point is fixed by an action-quotient Sylow. Lifting
that Sylow gives the full ambient two-part. A nonsingular centralizer is
contained in M by the earlier source input. Its index in M is the index
of its literal stabilizer in the action quotient, namely 120 or 496.
Thus its two-part is strictly less than half the ambient Sylow order.
The argument does not require the action kernel to be a two-group.

Source: Aschbacher--Smith H.9.1 and 12.1.5(2), printed pp.389--390,791.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

private theorem ambient_sylow_card (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (P : Sylow 2 (normalizer (L : Set G))) : Nat.card P = Nat.card T := by
  have he : Nat.card P = Nat.card (T.subtype hTM) := by
    rw [P.card_eq_multiplicity, (T.subtype hTM).card_eq_multiplicity]
  exact he.trans (Nat.card_congr (subgroupOfEquivOfLe hTM).toEquiv)

omit [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))] in
private theorem centralizerTwoPart_le (w : componentOrbit V (T : Subgroup G)) :
    B.centralizerTwoPart w ≤ Nat.card T := by
  let P : Sylow 2 (centralizer ({(w : G)} : Set G)) := Classical.choice inferInstance
  obtain ⟨R, hR⟩ := (P.isPGroup'.map (centralizer ({(w : G)} : Set G)).subtype).exists_le_sylow
  have hc := card_le_of_le hR
  rw [card_map_of_injective (centralizer ({(w : G)} : Set G)).subtype_injective,
    P.card_eq_multiplicity, R.card_eq_multiplicity, ← T.card_eq_multiplicity] at hc
  exact hc

namespace SourceModel
variable (S : B.SourceModel)
include S

/-- The singular diagonal class has full ambient Sylow two-part. -/
theorem diagonal_twoPart
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : B.IsSingularDiagonal w) :
    B.centralizerTwoPart w = Nat.card T := by
  have hne : w ≠ 1 := by
    intro he
    exact hw.1 (by rw [he, map_one]; rfl)
  obtain ⟨Pbar, hfix⟩ := (S.setup.singularDiagonal_iff_sylow hne).mp
    ((S.singularDiagonal_iff w).mpr hw)
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective B.actionProjection_surjective 2 Pbar
  have hPC : (P : Subgroup (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype ≤ centralizer ({(w : G)} : Set G) := by
    rintro x ⟨m, hm, rfl⟩
    have hf : B.actionProjection m ∈ (Pbar : Subgroup _) := by
      rw [← hP]
      exact mem_map_of_mem _ hm
    have hs : B.actionProjection m ∈ S.setup.stabilizer (Additive.ofMul w) := hfix _ hf
    change m ∈ (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection at hs
    rwa [S.stabilizer_comap] at hs
  let A := (P : Subgroup (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype
  obtain ⟨R, hR⟩ := ((P.isPGroup'.map (normalizer (L : Set G)).subtype).comap_subtype
    (K := centralizer ({(w : G)} : Set G))).exists_le_sylow
  have hcard := card_le_of_le hR
  change Nat.card (A.subgroupOf (centralizer ({(w : G)} : Set G))) ≤ Nat.card R at hcard
  rw [Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv,
    card_map_of_injective (normalizer (L : Set G)).subtype_injective,
    ambient_sylow_card hTM P, R.card_eq_multiplicity] at hcard
  exact le_antisymm (centralizerTwoPart_le w) hcard

omit [Finite G] in
/-- The two nonsingular stabilizer indices are computed in the actual quotient. -/
theorem nonsingular_stabilizer_index
    (w : componentOrbit V (T : Subgroup G)) (hw : B.quadratic (Additive.ofMul w) = 1) :
    (S.setup.stabilizer (Additive.ofMul w)).index = 120 ∨
      (S.setup.stabilizer (Additive.ofMul w)).index = 496 := by
  have hpair : (S.setup.model.coordinates (Additive.ofMul w)).2
      (S.setup.model.coordinates (Additive.ofMul w)).1 = 1 := by
    simpa only [← S.quadratic_eq, S.setup.quadratic_apply,
      BinaryNaturalDual.quadratic_apply] using hw
  have hcard := Nat.card_congr (S.setup.stabilizerEquiv (Additive.ofMul w)).toEquiv
  have hgroup := Nat.card_congr S.setup.model.group.toEquiv
  have hidx := (S.setup.stabilizer (Additive.ofMul w)).index_mul_card
  rcases S.setup.degree with hn | hn
  · subst n
    have hs := BinaryNaturalDual.VectorStabilizers.fullStabilizer_card_four
      (BinaryNaturalDual.ModelOrbits.AutomorphismModel.coordinateAction (Or.inl rfl)) hpair
    have hg := BinaryNaturalDual.AdaptedPair.Four.UpperSylow.automorphismGroup_card
      (BinaryNaturalDual.ModelOrbits.AutomorphismModel.coordinateAction (Or.inl rfl))
      (BinaryNaturalDual.ModelOrbits.AutomorphismModel.inner_index (Or.inl rfl))
    rw [hcard, hs, hgroup, hg] at hidx
    left
    omega
  · subst n
    have hs := BinaryNaturalDual.VectorStabilizers.fullStabilizer_card_five
      (BinaryNaturalDual.ModelOrbits.AutomorphismModel.coordinateAction (Or.inr rfl)) hpair
    let d := BinaryNaturalDual.ModelOrbits.AutomorphismModel.coordinateAction (Or.inr rfl : 5 = 4 ∨ 5 = 5)
    have hg := (BinaryNaturalDual.AdaptedPair.standardGroup 5).index_mul_card
    rw [BinaryNaturalDual.AdaptedPair.Five.standardGroup_index d
      (BinaryNaturalDual.ModelOrbits.AutomorphismModel.inner_index (Or.inr rfl)),
      BinaryNaturalDual.AdaptedPair.Five.standardGroup_card d] at hg
    rw [hcard, hs, hgroup, ← hg] at hidx
    right
    omega

end SourceModel

private theorem twice_twoPart_lt_of_index {A : Type*} [Group A] [Finite A]
    (H : Subgroup A) (hi : H.index = 120 ∨ H.index = 496) :
    2 * 2 ^ (Nat.card H).factorization 2 < 2 ^ (Nat.card A).factorization 2 := by
  have hpos : 0 < 2 ^ (Nat.card H).factorization 2 := pow_pos (by decide) _
  have hidx := H.index_mul_card
  have hf := congrArg (fun k : ℕ => k.factorization 2) hidx
  rcases hi with hi | hi
  · rw [hi, Nat.factorization_mul (by decide) Nat.card_pos.ne'] at hf
    have hval : (Nat.factorization 120) 2 = 3 := by decide +kernel
    simp only [Finsupp.add_apply, hval] at hf
    rw [← hf, pow_add]
    norm_num
  · rw [hi, Nat.factorization_mul (by decide) Nat.card_pos.ne'] at hf
    have hval : (Nat.factorization 496) 2 = 4 := by decide +kernel
    simp only [Finsupp.add_apply, hval] at hf
    rw [← hf, pow_add]
    norm_num

namespace SourceModel
variable (S : B.SourceModel)
include S

/-- Nonsingular ambient containment and the quotient index give strict separation. -/
theorem nonsingular_twoPart
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hc : B.NonsingularCentralizers)
    (w : componentOrbit V (T : Subgroup G)) (hw : B.quadratic (Additive.ofMul w) = 1) :
    2 * B.centralizerTwoPart w < Nat.card T := by
  let C := centralizer ({(w : G)} : Set G)
  let M := normalizer (L : Set G)
  have hCM : C ≤ M := hc w (hw.trans_ne one_ne_zero)
  have hi : (C.subgroupOf M).index = (S.setup.stabilizer (Additive.ofMul w)).index := by
    rw [← S.stabilizer_comap]
    exact index_comap_of_surjective _ B.actionProjection_surjective
  have hbound := twice_twoPart_lt_of_index (C.subgroupOf M)
    (hi ▸ S.nonsingular_stabilizer_index w hw)
  rw [Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv,
    ← (T.subtype hTM).card_eq_multiplicity, ambient_sylow_card hTM] at hbound
  exact hbound

/-- All three ambient orders, from the one original marked Sylow assertion. -/
theorem centralizerOrders_of_marked
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hc : B.NonsingularCentralizers) (hs : S.MarkedAmbientSylow hTM) :
    B.CentralizerOrders :=
  ⟨S.pure_twoPart_of_marked hTM hs, S.diagonal_twoPart hTM,
    S.nonsingular_twoPart hTM hc⟩

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
