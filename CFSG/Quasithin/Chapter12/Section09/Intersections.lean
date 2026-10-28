module

public import CFSG.Quasithin.Chapter12.Section08.Setup
public import Theory.GroupTheory.ConjugateIntersectionCore

/-!
# Intersection and normalizer deductions in Section 12.9

Transport the actual intersection to a term of the invariant flag. The
12.8.3 transporter then replaces the original conjugator by an element of
that flag normalizer. Assuming the earlier 12.9.7 normalizer bounds, an
intersection of order greater than two forces equality of the conjugates.
Consequently every subspace of order greater than two controls its normalizer.

These are conditional deductions from 12.9.7; the local analysis supplying
that result is not a field of the original natural-module hypothesis.
Source: Aschbacher--Smith, 12.9.8(1), printed p.862, and its applications
in 12.9.9 and the end of 12.9.1, pp.862--864.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

omit [Finite G] in
private theorem right_conjugate_mul (A : Subgroup G) (a b : G) :
    conjugate A (a * b) = conjugate (conjugate A a) b := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- The intersection assertion of 12.9.8(1), conditional on 12.9.7. -/
theorem intersection_card_le_two
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (hcontrol : ∀ i, 1 < i → i < n → F.Gi i ≤ normalizer (V : Set G))
    (g : G) (hg : g ∉ normalizer (V : Set G)) :
    Nat.card (V ⊓ conjugate V g : Subgroup G) ≤ 2 := by
  let :=  h.chosen.elementary
  let B : Subgroup G := V ⊓ conjugate V g
  have hp : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 V).to_le inf_le_left
  obtain ⟨i, hi⟩ := hp.exists_card_eq
  have hin : i ≤ n := by
    have hc := Nat.card_le_card_of_injective (inclusion (show B ≤ V from inf_le_left))
      (inclusion_injective _)
    rw [hi, h.seed_card] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  by_contra hbig
  have htwo : 1 < i := by
    by_contra hn
    have hpow : 2 ^ i ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [pow_one] at hpow
    rw [hi] at hbig
    omega
  obtain ⟨l, hl, hbl⟩ := h.subspace_transitive B (F.Vi i) inf_le_left (F.le_seed i)
    (hi.trans (F.card i hin).symm)
  have hp : F.Vi i ≤ conjugate V (g * l) := by
    rw [right_conjugate_mul, ← hbl]
    exact map_mono (show B ≤ conjugate V g from inf_le_right)
  obtain ⟨k, hk, he⟩ := h.flag_transporter F i (g * l) hp
  have hkn : k ∈ normalizer (V : Set G) := by
    by_cases hin' : i < n
    · exact hcontrol i htwo hin' hk
    · have he : i = n := by omega
      simpa only [he, InvariantFlag.Gi, F.last] using hk
  have hgl : g * l ∈ normalizer (V : Set G) :=
    (conjugate_eq_iff _ _).mp (he.trans ((conjugate_eq_iff _ _).mpr hkn))
  apply hg
  simpa only [mul_inv_cancel_right] using (normalizer (V : Set G)).mul_mem hgl
    ((normalizer (V : Set G)).inv_mem (h.chosen.normalizes hl))

/-- Every noncyclic subspace controls its normalizer after 12.9.7. -/
theorem subspace_normalizer_le
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (hcontrol : ∀ i, 1 < i → i < n → F.Gi i ≤ normalizer (V : Set G))
    {B : Subgroup G} (hBV : B ≤ V) (hB : 2 < Nat.card B) :
    normalizer (B : Set G) ≤ normalizer (V : Set G) := by
  apply normalizer_le_of_conjugate_intersection_card_bound hBV hB
  intro g hg
  have hn : g⁻¹ ∉ normalizer (V : Set G) := by
    intro hi
    exact hg (by simpa using (normalizer (V : Set G)).inv_mem hi)
  simpa only [conjugate, inv_inv] using intersection_card_le_two h F hcontrol g⁻¹ hn

/-- Both clauses of 12.9.8 and the normalizer consequence used in 12.9.9,
from the actual abelian conclusion of 12.9.4 and the actual 12.9.7 bounds.
Their source proofs remain with the natural-branch producer. -/
theorem source_intersections_of_local_geometry
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (habelian : IsMulCommutative F.U)
    (hcontrol : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V) :
    (∀ g : G, g ∉ normalizer (L : Set G) →
      Nat.card (V ⊓ conjugate V g : Subgroup G) ≤ 2) ∧
    (∀ g : G, V ⊓ conjugate V g ≠ ⊥ → ⁅V, conjugate V g⁆ = ⊥) ∧
    (∀ B : Subgroup G, B ≤ V → 2 < Nat.card B →
      normalizer (B : Set G) ≤ normalizer (V : Set G)) := by
  have hc : ∀ i, 1 < i → i < n → F.Gi i ≤ normalizer (V : Set G) :=
    fun i hi hin => (hcontrol i hi hin).trans inf_le_right
  refine ⟨?_, (h.abelian_source_geometry earlier F).2.mp habelian, ?_⟩
  · intro g hg
    exact intersection_card_le_two h F hc g
      (fun hn => hg (h.seed_normalizer_le earlier.structural earlier.uniqueness hn))
  · intro B hBV hB
    exact subspace_normalizer_le h F hc hBV hB

end CFSG.Quasithin.Chapter12.Section09
