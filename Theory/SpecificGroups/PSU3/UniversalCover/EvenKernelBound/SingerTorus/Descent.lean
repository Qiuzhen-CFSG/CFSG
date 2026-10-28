module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.Order


/-!
# Descent and indices for a special-unitary Singer torus

A cyclic subgroup T of SU₃(q) of order q²−q+1 containing the actual scalar
kernel maps to a cyclic subgroup of PSU₃(q) of order
(q²−q+1)/gcd(3,q+1). Its index is q³(q−1)(q+1)². The scalar containment
identifies the full inverse image, so normalizers and their relative index
also descend through the literal special-to-projective map.

These are conditional descent results: neither a special-unitary Singer
torus nor its normalizer of relative index three is constructed here.
`image_configuration` and `image_sylow_configuration` consume those exact
inputs. `standard_configuration_transport` carries the resulting actual
projective subgroup to an arbitrary Hermitian form with the same involution.

Source: GLS III, Theorem 6.5.3(c) and its proof (refs/KGroup/GLS3/chapter6.tex,
printed pp.346–347). The projective order uses Huppert II.10.12. For q=8,
the special torus order is 57 and its projective image has order 19, so the
scalar divisor cannot be omitted even in characteristic two.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.SingerTorus
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- The exact image order, retaining the full scalar quotient. -/
theorem image_card (T : Subgroup J.specialSubgroup)
    (hk : J.specialToProjective.ker ≤ T) {q : ℕ}
    (hT : Nat.card T = q ^ 2 - q + 1)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    Nat.card (T.map J.specialToProjective) =
      (q ^ 2 - q + 1) / Nat.gcd 3 (q + 1) := by
  have hm := relIndex_mul_relIndex (⊥ : Subgroup J.specialSubgroup)
    J.specialToProjective.ker T bot_le hk
  rw [relIndex_bot_left, relIndex_bot_left, relIndex_ker] at hm
  have hd := Nat.card_pos (α := J.specialToProjective.ker)
  rw [card_kernel J hcard hconj] at hm hd
  rw [← hT, ← hm, Nat.mul_div_right _ hd]

omit [Finite F] in
/-- Scalar containment identifies the normalizer of the actual projective image. -/
theorem image_normalizer (T : Subgroup J.specialSubgroup)
    (hk : J.specialToProjective.ker ≤ T) :
    (normalizer (T : Set _)).map J.specialToProjective = (normalizer (T.map J.specialToProjective : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  calc
    _ = ((normalizer (T.map J.specialToProjective : Set (ProjectiveSpecialUnitaryMatrixGroup J))).comap J.specialToProjective).map
        J.specialToProjective := by
      rw [comap_normalizer_eq_of_surjective _ J.specialToProjective_surjective,
        comap_map_eq_self hk]
    _ = _ := map_comap_eq_self (fun g _ => J.specialToProjective_surjective g)

omit [Finite F] in
/-- The relative normalizer index is unchanged by this central quotient. -/
theorem image_normalizer_relIndex (T : Subgroup J.specialSubgroup)
    (hk : J.specialToProjective.ker ≤ T) :
    (T.map J.specialToProjective).relIndex (normalizer (T.map J.specialToProjective : Set (ProjectiveSpecialUnitaryMatrixGroup J))) =
      T.relIndex (normalizer (T : Set _)) := by
  rw [← image_normalizer J T hk, relIndex_map_map,
    sup_eq_left.mpr hk, sup_eq_left.mpr (hk.trans T.le_normalizer)]

private theorem cubic_factor {q : ℕ} (hq : 1 < q) :
    q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
  have hs := Nat.sub_add_cancel (show q ≤ q ^ 2 by nlinarith)
  have hh := congrArg (fun a : ℕ => (q + 1) * a) hs
  nlinarith

/-- The projective index of a special-unitary torus of the Singer order. -/
theorem image_index (T : Subgroup J.specialSubgroup)
    (hk : J.specialToProjective.ker ≤ T) {q : ℕ} (hq : 1 < q)
    (hT : Nat.card T = q ^ 2 - q + 1)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    (T.map J.specialToProjective).index = q ^ 3 * (q - 1) * (q + 1) ^ 2 := by
  have hd : Nat.gcd 3 (q + 1) ∣ q ^ 2 - q + 1 := by
    rw [← hT, ← card_kernel J hcard hconj]
    exact card_dvd_of_le hk
  have hs : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq q 1
  have he : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
      Nat.card (T.map J.specialToProjective) * (q ^ 3 * (q - 1) * (q + 1) ^ 2) := by
    rw [OddKernelBound.OddCrossCharacteristic.card_projective J hcard hconj, image_card J T hk hT hcard hconj,
      cubic_factor hq, hs]
    calc
      _ = ((q ^ 3 * (q - 1) * (q + 1) ^ 2) * (q ^ 2 - q + 1)) /
          Nat.gcd 3 (q + 1) := by congr 1; ring
      _ = _ := by rw [Nat.mul_div_assoc _ hd]; ring
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos
    ((T.map J.specialToProjective).card_mul_index.trans he)

/-- A prime above three in the Singer factor misses the torus index. -/
theorem not_dvd_index {q p : ℕ} (hq : 1 < q) (hp : p.Prime)
    (hp3 : 3 < p) (hd : p ∣ q ^ 2 - q + 1) :
    ¬ p ∣ q ^ 3 * (q - 1) * (q + 1) ^ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hle : q ≤ q ^ 2 := by nlinarith
  have hz : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ p).mpr hd
    simpa only [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one] using h
  have hnq : ¬ p ∣ q := by
    intro h
    have h0 := (ZMod.natCast_eq_zero_iff q p).mpr h
    simp [h0] at hz
  have hnminus : ¬ p ∣ q - 1 := by
    intro h
    have hm := (ZMod.natCast_eq_zero_iff (q - 1) p).mpr h
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one, sub_eq_zero] at hm
    simp [hm] at hz
  have hnplus : ¬ p ∣ q + 1 := by
    intro h
    have hm := (ZMod.natCast_eq_zero_iff (q + 1) p).mpr h
    have hm' : (q : ZMod p) = -1 := by push_cast at hm; exact eq_neg_of_add_eq_zero_left hm
    have h3 : (3 : ZMod p) = 0 := by rw [hm'] at hz; norm_num at hz ⊢; exact hz
    have hh := Nat.le_of_dvd (by decide : 0 < 3) ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
    omega
  exact hp.not_dvd_mul (hp.not_dvd_mul (fun h => hnq (hp.dvd_of_dvd_pow h)) hnminus)
    (fun h => hnplus (hp.dvd_of_dvd_pow h))


/-- All projective cardinalities and indices from an actual special torus and its normalizer. -/
theorem image_configuration (T : Subgroup J.specialSubgroup) [IsCyclic T]
    (hk : J.specialToProjective.ker ≤ T) {q : ℕ} (hq : 1 < q)
    (hT : Nat.card T = q ^ 2 - q + 1)
    (hN : T.relIndex (normalizer (T : Set _)) = 3)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    IsCyclic (T.map J.specialToProjective) ∧
    Nat.card (T.map J.specialToProjective) = (q ^ 2 - q + 1) / Nat.gcd 3 (q + 1) ∧
    (T.map J.specialToProjective).index = q ^ 3 * (q - 1) * (q + 1) ^ 2 ∧
    (T.map J.specialToProjective).relIndex
      (normalizer (T.map J.specialToProjective : Set (ProjectiveSpecialUnitaryMatrixGroup J))) = 3 ∧
    Nat.card (normalizer (T.map J.specialToProjective : Set (ProjectiveSpecialUnitaryMatrixGroup J))) =
      3 * ((q ^ 2 - q + 1) / Nat.gcd 3 (q + 1)) ∧
    (normalizer (T.map J.specialToProjective : Set (ProjectiveSpecialUnitaryMatrixGroup J))).index =
      (q ^ 3 * (q - 1) * (q + 1) ^ 2) / 3 := by
  have hc := image_card J T hk hT hcard hconj
  have hi := image_index J T hk hq hT hcard hconj
  have hn : (T.map J.specialToProjective).relIndex
      (normalizer (T.map J.specialToProjective : Set (ProjectiveSpecialUnitaryMatrixGroup J))) = 3 := by
    rw [image_normalizer_relIndex J T hk, hN]
  refine ⟨isCyclic_of_surjective (J.specialToProjective.subgroupMap T)
    (J.specialToProjective.subgroupMap_surjective T), hc, hi, hn, ?_, ?_⟩
  · have hm := relIndex_mul_relIndex (⊥ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
      (T.map J.specialToProjective) (normalizer (T.map J.specialToProjective : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
      bot_le (T.map J.specialToProjective).le_normalizer
    rw [relIndex_bot_left, relIndex_bot_left, hn, hc] at hm
    exact hm.symm.trans (mul_comm _ _)
  · have hm := relIndex_mul_index (T.map J.specialToProjective).le_normalizer
    rw [hn, hi] at hm
    rw [← hm, Nat.mul_div_right _ (by decide : 0 < 3)]

/-- The actual projective torus contains a cyclic ambient Sylow subgroup. -/
theorem image_sylow_configuration (T : Subgroup J.specialSubgroup) [IsCyclic T]
    (hk : J.specialToProjective.ker ≤ T) {q p : ℕ} (hq : 1 < q)
    (hT : Nat.card T = q ^ 2 - q + 1)
    (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ q ^ 2 - q + 1)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    ∃ Q : Sylow p (ProjectiveSpecialUnitaryMatrixGroup J),
      (Q : Subgroup _) ≤ T.map J.specialToProjective ∧ IsCyclic Q := by
  let : Fact p.Prime := ⟨hp⟩
  let H := T.map J.specialToProjective
  let : IsCyclic H := isCyclic_of_surjective (J.specialToProjective.subgroupMap T)
    (J.specialToProjective.subgroupMap_surjective T)
  let P : Sylow p H := Classical.choice inferInstance
  let R : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) := (P : Subgroup H).map H.subtype
  have hi : ¬ p ∣ H.index := by
    rw [image_index J T hk hq hT hcard hconj]
    exact not_dvd_index hq hp hp3 hd
  have hRi : ¬ p ∣ R.index := by
    rw [show R.index = (P : Subgroup H).index * H.index from index_map_subtype _]
    exact hp.not_dvd_mul P.not_dvd_index hi
  let Q : Sylow p (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (P.isPGroup'.map H.subtype).toSylow hRi
  refine ⟨Q, map_subtype_le _, ?_⟩
  let e : P ≃* R := (P : Subgroup H).equivMapOfInjective H.subtype H.subtype_injective
  exact e.isCyclic.mp inferInstance

/-- Transport the marked projective torus and its relative normalizer index to the original form. -/
theorem standard_configuration_transport {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup (FormTransport.standardForm J)))
    [IsCyclic H] (hH : Nat.card H = (q ^ 2 - q + 1) / Nat.gcd 3 (q + 1))
    (hi : H.index = q ^ 3 * (q - 1) * (q + 1) ^ 2)
    (hN : H.relIndex (normalizer (H : Set _)) = 3) :
    ∃ T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      IsCyclic T ∧ Nat.card T = (q ^ 2 - q + 1) / Nat.gcd 3 (q + 1) ∧
      T.index = q ^ 3 * (q - 1) * (q + 1) ^ 2 ∧
      T.relIndex (normalizer (T : Set _)) = 3 := by
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J q hcard (card_fixed J hcard hconj)
  let T := H.map e.symm.toMonoidHom
  refine ⟨T, (H.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).isCyclic.mp
    inferInstance, ?_, ?_, ?_⟩
  · exact (card_map_of_injective e.symm.injective).trans hH
  · exact (index_map_equiv H e.symm).trans hi
  · change (H.map e.symm.toMonoidHom).relIndex (normalizer (H.map e.symm.toMonoidHom : Set _)) = 3
    rw [← map_normalizer_eq_of_bijective H e.symm.bijective,
      relIndex_map_map_of_injective H _ e.symm.injective, hN]

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.SingerTorus
