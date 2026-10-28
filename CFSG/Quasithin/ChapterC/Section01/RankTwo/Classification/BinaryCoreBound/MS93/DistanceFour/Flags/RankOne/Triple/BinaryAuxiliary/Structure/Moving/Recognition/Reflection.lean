module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Recognition.Space
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# A small reflection bounds the full binary moving space

The full moving space lies in the orbit span of a reflection displacement:
conjugate reflections generate S3. If the displacement has at most two
vectors, choose a generator v. The cubic norm preserves its displacement,
so the norm of v is either zero or v. In the first case the cubic orbit lies
in the span of v and rv; in the second case v is cubic-fixed. The reflection
fixes v in both cases. Thus every orbit vector lies in a binary plane image,
which has at most four vectors.

This argument permits an arbitrary fixed summand in the ambient representation.
It bounds the full actor's moving space, including all reflection differences.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
open Incident.Pairing.Transport.Natural.Kernel
open BinaryS3

private theorem reflection_words : ∀ t : Actor, t ^ 2 = 1 → t ≠ 1 →
    ∀ g : Actor, g = 1 ∨ g = cubic ∨ g = cubic ^ 2 ∨
      g = t ∨ g = cubic * t ∨ g = cubic ^ 2 * t := by decide +kernel

private theorem cubic_factor : ∀ t : Actor, t ^ 2 = 1 → t ≠ 1 →
    cubic = t * (cubic * t * cubic⁻¹) := by decide +kernel

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) Actor W)

private lemma double (v : W) : v + v = 0 := by
  have h := @two_smul (ZMod 2) W _ _ _ v
  have ht : (2 : ZMod 2) = 0 := by decide
  rw [ht, zero_smul] at h
  exact h.symm

private lemma neg_self (v : W) : -v = v := neg_eq_iff_add_eq_zero.mpr (double v)

private lemma orbitSpan_stable (D : Submodule (ZMod 2) W) (g : Actor)
    {v : W} (hv : v ∈ orbitSpan ρ D) : ρ g v ∈ orbitSpan ρ D := by
  have hle : orbitSpan ρ D ≤ (orbitSpan ρ D).comap (ρ g) := by
    apply iSup_le
    intro h
    rintro _ ⟨w, hw, rfl⟩
    exact (le_iSup (fun k : Actor => D.map (ρ k)) (g * h))
      ⟨w, hw, by simp only [map_mul, Module.End.mul_apply]⟩
  exact hle hv

private lemma moving_le_orbitSpan (t : Actor) (ht : t ^ 2 = 1) (htn : t ≠ 1) :
    (movedSpace ρ).toSubmodule ≤ orbitSpan ρ (displacement ρ t) := by
  let U := orbitSpan ρ (displacement ρ t)
  have hD : displacement ρ t ≤ U := by
    intro v hv
    exact (le_iSup (fun g : Actor => (displacement ρ t).map (ρ g)) 1)
      ⟨v, hv, by simp⟩
  have hmul (a b : Actor)
      (ha : ∀ w, ρ a w - w ∈ U) (hb : ∀ w, ρ b w - w ∈ U) :
      ∀ w, ρ (a * b) w - w ∈ U := by
    intro w
    have hh := U.add_mem (orbitSpan_stable ρ _ a (hb w)) (ha w)
    have he : ρ a (ρ b w - w) + (ρ a w - w) = ρ (a * b) w - w := by
      rw [map_sub, map_mul, Module.End.mul_apply]
      abel
    exact he ▸ hh
  have hT (w : W) : ρ t w - w ∈ U := hD ⟨w, rfl⟩
  have hconj (w : W) : ρ (cubic * t * cubic⁻¹) w - w ∈ U := by
    have hh := orbitSpan_stable ρ (displacement ρ t) cubic (hT (ρ cubic⁻¹ w))
    have he : ρ cubic (ρ t (ρ cubic⁻¹ w) - ρ cubic⁻¹ w) =
        ρ (cubic * t * cubic⁻¹) w - w := by
      rw [map_sub]
      simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply, mul_assoc]
    exact he ▸ hh
  have hC (w : W) : ρ cubic w - w ∈ U := by
    rw [cubic_factor t ht htn]
    exact hmul t (cubic * t * cubic⁻¹) hT hconj w
  have hC2 (w : W) : ρ (cubic ^ 2) w - w ∈ U := by
    rw [pow_two]
    exact hmul cubic cubic hC hC w
  apply Submodule.span_le.mpr
  rintro _ ⟨g, _, w, _, rfl⟩
  rcases reflection_words t ht htn g with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [map_one, Module.End.one_apply, sub_self]
    exact U.zero_mem
  · exact hC w
  · exact hC2 w
  · exact hT w
  · exact hmul cubic t hC hT w
  · exact hmul (cubic ^ 2) t hC2 hT w

private lemma exists_generator_of_card_le_two [Finite W] (D : Submodule (ZMod 2) W)
    (hc : Nat.card D ≤ 2) : ∃ v ∈ D, ∀ w ∈ D, w = 0 ∨ w = v := by
  by_cases hone : Nat.card D ≤ 1
  · let : Subsingleton D := Finite.card_le_one_iff_subsingleton.mp hone
    refine ⟨0, D.zero_mem, fun w hw => Or.inl ?_⟩
    exact congrArg Subtype.val (Subsingleton.elim (⟨w, hw⟩ : D) 0)
  · have htwo : Nat.card D = 2 := le_antisymm hc (Nat.succ_le_of_lt (lt_of_not_ge hone))
    obtain ⟨v, hv, hu⟩ := (Nat.card_eq_two_iff' (0 : D)).mp htwo
    refine ⟨v, v.property, fun w hw => ?_⟩
    by_cases hw0 : w = 0
    · exact Or.inl hw0
    · exact Or.inr (congrArg Subtype.val (hu ⟨w, hw⟩ (fun he => hw0 (congrArg Subtype.val he))))

private def planeMap (v : W) : (ZMod 2 × ZMod 2) →ₗ[ZMod 2] W where
  toFun x := x.1 • v + x.2 • ρ cubic v
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' c x := by simp [smul_add, mul_smul]

private lemma displacement_fixed (t : Actor) (ht : t ^ 2 = 1)
    {v : W} (hv : v ∈ displacement ρ t) : ρ t v = v := by
  obtain ⟨w, rfl⟩ := hv
  have he : ρ t (ρ t w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, ht, map_one]
    rfl
  change ρ t (ρ t w - w) = ρ t w - w
  rw [map_sub, he]
  simp only [sub_eq_add_neg, neg_self]
  abel

private lemma orbitSpan_le_plane [Finite W] (t : Actor) (ht : t ^ 2 = 1) (htn : t ≠ 1)
    (hc : Nat.card (displacement ρ t) ≤ 2) :
    ∃ v : W, orbitSpan ρ (displacement ρ t) ≤ LinearMap.range (planeMap ρ v) := by
  obtain ⟨v, hv, hgen⟩ := exists_generator_of_card_le_two (displacement ρ t) hc
  let U := LinearMap.range (planeMap ρ v)
  have hvU : v ∈ U := ⟨(1, 0), by simp [planeMap]⟩
  have hrvU : ρ cubic v ∈ U := ⟨(0, 1), by simp [planeMap]⟩
  have hr2U : ρ (cubic ^ 2) v ∈ U := by
    rcases hgen (norm ρ v) (norm_mem_displacement ρ t hv) with hn | hn
    · have he : ρ (cubic ^ 2) v = v + ρ cubic v := by
        rw [norm_apply] at hn
        have h := eq_neg_of_add_eq_zero_right hn
        simpa only [neg_self] using h
      rw [he]
      exact U.add_mem hvU hrvU
    · have he : ρ cubic v = v := by
        have hh := norm_fixed ρ v
        rwa [hn] at hh
      rw [pow_two, map_mul, Module.End.mul_apply, he, he]
      exact hvU
  have horbit (g : Actor) : ρ g v ∈ U := by
    have hf := displacement_fixed ρ t ht hv
    rcases reflection_words t ht htn g with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using hvU
    · exact hrvU
    · exact hr2U
    · rwa [hf]
    · simpa only [map_mul, Module.End.mul_apply, hf] using hrvU
    · simpa only [map_mul, Module.End.mul_apply, hf] using hr2U
  refine ⟨v, iSup_le fun g => ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  rcases hgen w hw with rfl | rfl
  · simpa only [map_zero] using U.zero_mem
  · exact horbit g

/-- One reflection of displacement order at most two bounds the entire
moving subspace by four, with no restriction on the ambient fixed space. -/
theorem smallReflectionBound : SmallReflectionBound := by
  intro W _ _ _ ρ t ht htn hc
  obtain ⟨v, hv⟩ := orbitSpan_le_plane ρ t ht htn hc
  have hle := (moving_le_orbitSpan ρ t ht htn).trans hv
  have h1 := Nat.card_le_card_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have h2 := Nat.card_le_card_of_surjective (planeMap ρ v).rangeRestrict
    (LinearMap.surjective_rangeRestrict (planeMap ρ v))
  have h4 : Nat.card (ZMod 2 × ZMod 2) = 4 := by simp
  exact h1.trans (h2.trans_eq h4)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
