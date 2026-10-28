module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Geometry
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PrimeRankCubeFree
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic
/-!
# Three-rank of the actual weight-four point-stabilizer residual

Two disjoint three-cycles, supported inside and outside the four-point set,
embed an elementary nine-group in its alternating stabilizer. Every element
of this group belongs to the two-residual by coprimeness. The three-part of
7! is nine, giving the reverse rank bound. The final transport theorem uses
the literal preimage of the point stabilizer along an injective actor map.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final argument
of Lemma 12.8.13(6), printed p.857. The argument applies to both A₇ and S₇.
-/

@[expose] public section
namespace BinaryPermutation.SevenParabolic
open Subgroup
private abbrev Nine := Multiplicative (ZMod 3 × ZMod 3)
private def cubicLeft : Equiv.Perm (Fin 7) := Equiv.swap 0 1 * Equiv.swap 1 2
private def cubicRight : Equiv.Perm (Fin 7) := Equiv.swap 4 5 * Equiv.swap 5 6
private def nineMap : Nine →* Equiv.Perm (Fin 7) where
  toFun i := cubicLeft ^ i.toAdd.1.val * cubicRight ^ i.toAdd.2.val
  map_one' := by decide
  map_mul' := by decide +kernel

private lemma nineMap_injective : Function.Injective nineMap := by decide +kernel
private lemma nineMap_even : ∀ i, nineMap i ∈ alternatingGroup (Fin 7) := by
  change ∀ i, Equiv.Perm.sign (nineMap i) = 1
  decide +kernel
private lemma nineMap_fixes : ∀ i, action (nineMap i) firstFour = firstFour := by
  decide +kernel
private lemma nine_pow_three : ∀ i : Nine, i ^ 3 = 1 := by decide
private instance nine_elementary : IsElementaryAbelian 3 Nine where
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr nine_pow_three

private lemma nine_rank : 2 ≤ primeRank 3 Nine := by
  let : IsElementaryAbelian 3 (⊤ : Subgroup Nine) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => Subtype.ext (nine_pow_three x.val)) }
  apply IsElementaryAbelian.primeRank_ge_of_card (p := 3) (⊤ : Subgroup Nine)
  rw [Nat.card_congr Subgroup.topEquiv.toEquiv]
  norm_num [Nine]

/-- An actual elementary nine-group in the even part of every weight-four point stabilizer. -/
lemma exists_nine_in_pointStabilizer (v : Space) (hv : weight v = 4) :
    ∃ f : Multiplicative (ZMod 3 × ZMod 3) →* Equiv.Perm (Fin 7),
      Function.Injective f ∧ ∀ i, f i ∈ alternatingGroup (Fin 7) ∧ action (f i) v = v := by
  obtain ⟨s, hs⟩ := exists_permutation_firstFour v hv
  let f := (MulAut.conj s⁻¹).toMonoidHom.comp nineMap
  refine ⟨f, (MulAut.conj s⁻¹).injective.comp nineMap_injective, ?_⟩
  intro i
  constructor
  · exact (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem _ (nineMap_even i) s⁻¹
  · change action (s⁻¹ * nineMap i * s) v = v
    simp only [map_mul, Module.End.mul_apply, hs, nineMap_fixes]
    rw [← hs]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]

lemma symmetric_threeRank_le : primeRank 3 (Equiv.Perm (Fin 7)) ≤ 2 := by
  apply primeRank_le_two_of_cube_not_dvd
  rw [Nat.card_perm, Nat.card_fin]
  decide

/-- The actual two-residual of a point stabilizer has three-rank two,
for either overgroup of A₇ inside S₇. -/
lemma pointResidual_threeRank (J : Subgroup (Equiv.Perm (Fin 7)))
    (hJ : alternatingGroup (Fin 7) ≤ J) (v : Space) (hv : weight v = 4) :
    primeRank 3 (pResidual 2 (J ⊓ pointStabilizer v : Subgroup (Equiv.Perm (Fin 7)))) = 2 := by
  let C := J ⊓ pointStabilizer v
  apply le_antisymm
  · exact (_root_.primeRank_le_of_injective 3
      (C.subtype.comp (pResidual 2 C).subtype)
      (Subtype.val_injective.comp Subtype.val_injective)).trans symmetric_threeRank_le
  · obtain ⟨f, hf, he⟩ := exists_nine_in_pointStabilizer v hv
    let j : Nine →* C := f.codRestrict C (fun i => ⟨hJ (he i).1, (he i).2⟩)
    have hj : Function.Injective j := fun x y h => hf (congrArg Subtype.val h)
    have hres (i : Nine) : j i ∈ pResidual 2 C := by
      apply mem_pResidual_of_orderOf_coprime
      have hpow : (j i) ^ 3 = 1 := by rw [← map_pow, nine_pow_three, map_one]
      exact (by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hpow)
    let k : Nine →* pResidual 2 C := j.codRestrict _ hres
    have hk : Function.Injective k := fun x y h => hj (congrArg Subtype.val h)
    exact nine_rank.trans (_root_.primeRank_le_of_injective 3 k hk)

/-- The same residual rank, pulled back along the actual actor embedding. -/
lemma actor_pointResidual_threeRank {A : Type*} [Group A] [Finite A]
    (f : A →* Equiv.Perm (Fin 7)) (hf : Function.Injective f)
    (hAlt : alternatingGroup (Fin 7) ≤ f.range) (v : Space) (hv : weight v = 4) :
    primeRank 3 (pResidual 2 ((pointStabilizer v).comap f)) = 2 := by
  let C := (pointStabilizer v).comap f
  have hc : C.map f = f.range ⊓ pointStabilizer v := by
    rw [Subgroup.map_comap_eq]
  let e := (Subgroup.equivMapOfInjective C f hf).trans (MulEquiv.subgroupCongr hc)
  let eR := (e.subgroupMap (pResidual 2 C)).trans
    (MulEquiv.subgroupCongr (map_pResidual 2 e))
  rw [primeRank_congr 3 eR]
  exact pointResidual_threeRank f.range hAlt v hv

lemma actor_point_threeRank_gt_one {A : Type*} [Group A] [Finite A]
    (f : A →* Equiv.Perm (Fin 7)) (hf : Function.Injective f)
    (hAlt : alternatingGroup (Fin 7) ≤ f.range) (v : Space) (hv : weight v = 4) :
    1 < primeRank 3 ((pointStabilizer v).comap f) := by
  have h := primeRank_subgroup_le 3 (pResidual 2 ((pointStabilizer v).comap f))
  rw [actor_pointResidual_threeRank f hf hAlt v hv] at h
  omega
end BinaryPermutation.SevenParabolic
