module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizerModel.Representatives
import Mathlib.Tactic

/-!
# Cubic conjugacy inside the concrete mu centralizer

An element of order three acts trivially on the first four letters, since
that action lies in a group of order eight. Its six-letter restriction has
cycle type (3) or (3,3). A symmetric-group conjugator on those letters can
be made even by multiplying its four-letter component by (01). Thus both
representatives are reached by actual elements of MuModel, which also fix
the marked central involution under conjugation.

Source: Held, DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/

public section

open Subgroup Equiv Equiv.Perm
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizer

@[expose] def first (n : ℕ) : Pair n →* Four :=
  (MonoidHom.fst _ _).comp (parity n).ker.subtype

theorem first_eq_one (x : Pair 6) (hx : orderOf x = 3) : x.val.1 = 1 := by
  have ha : orderOf x.val.1 ∣ 3 := hx ▸ orderOf_map_dvd (first 6) x
  have hb : orderOf x.val.1 ∣ 8 := four_card ▸ orderOf_dvd_natCard x.val.1
  have h := Nat.dvd_gcd ha hb
  norm_num at h
  exact h

theorem tail_order (x : Pair 6) (hx : orderOf x = 3) : orderOf x.val.2 = 3 := by
  apply orderOf_eq_prime
  · have h : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
    exact congrArg (fun y : Pair 6 => y.val.2) h
  · intro h
    have he : x = 1 := Subtype.ext (Prod.ext (first_eq_one x hx) h)
    simp [he] at hx

theorem tail_classes (p : Perm (Fin 6)) (hp : orderOf p = 3) :
    ∃ t : Bool, IsConj p (Tail.root t) := by
  obtain ⟨k, hk⟩ := cycleType_prime_order (σ := p) (hp ▸ Nat.prime_three)
  rw [hp] at hk
  have hb := p.sum_cycleType_le
  rw [hk, Multiset.sum_replicate] at hb
  simp only [smul_eq_mul, Fintype.card_fin] at hb
  have hkle : k ≤ 1 := by omega
  interval_cases k
  · refine ⟨false, isConj_of_cycleType_eq ?_⟩
    have hr : (Tail.root false).cycleType = {3} := by decide +kernel
    simpa [hr, Multiset.replicate_succ] using hk
  · refine ⟨true, isConj_of_cycleType_eq ?_⟩
    have hr : (Tail.root true).cycleType = {3, 3} := by decide +kernel
    simpa [hr, Multiset.replicate_succ] using hk

@[expose] def liftPermutation (p : Perm (Fin 6)) : Pair 6 :=
  ⟨(if sign p = 1 then 1 else flip, p), by
    change sign ((if sign p = 1 then 1 else flip) : Four).val * sign p = 1
    rcases Int.units_eq_one_or (sign p) with h | h
    · simp [h]
    · simp [h, flip]⟩

theorem pair_conjugacy (x : Pair 6) (hx : orderOf x = 3) :
    ∃ t : Bool, ∃ q : Pair 6, q * x * q⁻¹ = repPair t := by
  obtain ⟨t, ht⟩ := tail_classes x.val.2 (tail_order x hx)
  obtain ⟨p, hp⟩ := isConj_iff.mp ht
  refine ⟨t, liftPermutation p, Subtype.ext ?_⟩
  apply Prod.ext
  · change (liftPermutation p).val.1 * x.val.1 * (liftPermutation p).val.1⁻¹ = 1
    rw [first_eq_one x hx, mul_one, mul_inv_cancel]
  · exact hp

theorem representative_conjugacy (c : MuModel) (hc : orderOf c = 3) :
    ∃ t : Bool, ∃ q : MuModel, q * c * q⁻¹ = representative t := by
  obtain ⟨t, q, hq⟩ := pair_conjugacy (muEquiv.symm c) ((muEquiv.symm.orderOf_eq c).trans hc)
  refine ⟨t, muEquiv q, ?_⟩
  change muEquiv q * c * (muEquiv q)⁻¹ = muEquiv (repPair t)
  simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using congrArg muEquiv hq

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizer
