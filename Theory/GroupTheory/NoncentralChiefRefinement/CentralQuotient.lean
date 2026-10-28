module

public import Theory.GroupTheory.NoncentralChiefRefinement.ResidualRestriction.Transport

/-!
# Noncentral chief factors through central surjections

Refine the central kernel first, then refine the normal interval above it.
The first part contributes no noncentral chief factors. The quotient map
identifies each section of the second part equivariantly, and Jordan–Hölder
compares this refinement with any prescribed complete chief series.

This is the central-cover transfer used in Aschbacher–Smith 14.7.68(2),
printed p.1071. No bound on the central kernel's order is needed.
-/

public section
noncomputable section
open Subgroup
namespace NoncentralChiefRefinement
variable {K H : Type*} [Group K] [Group H]

/-- Centrality of an interval above the kernel is detected in the quotient. -/
theorem quotient_isCentral_iff (Q A B : NormalNode K) (hQA : Q ≤ A) :
    IsCentral (quotientImage Q A) (quotientImage Q B) ↔ IsCentral A B := by
  rw [isCentral_iff_action, isCentral_iff_action]
  constructor
  · intro h k x
    apply (quotientSectionEquiv Q A B hQA).injective
    rw [quotientSectionEquiv_equivariant, h]
  · intro h k x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective Q.val k
    obtain ⟨x, rfl⟩ := (quotientSectionEquiv Q A B hQA).surjective x
    rw [← quotientSectionEquiv_equivariant, h]

/-- Prime-group structure and the actual nontrivial action are both preserved. -/
theorem quotient_isNoncentralTwo_iff (Q A B : NormalNode K) (hQA : Q ≤ A) :
    IsNoncentralTwo (quotientImage Q A) (quotientImage Q B) ↔ IsNoncentralTwo A B :=
  and_congr ⟨fun h => h.of_equiv (quotientSectionEquiv Q A B hQA).symm,
    fun h => h.of_equiv (quotientSectionEquiv Q A B hQA)⟩
    (not_congr (quotient_isCentral_iff Q A B hQA))

/-- Project a chief series whose initial term contains the quotient kernel. -/
@[expose] def ChiefSeries.mapQuotient (s : ChiefSeries K) (Q : NormalNode K)
    (hQ : Q ≤ s.head) : ChiefSeries (K ⧸ Q.val) where
  length := s.length
  toFun i := quotientImage Q (s i)
  step i := (quotientImage_covBy_iff Q _ _
    (hQ.trans (CompositionSeries.head_le (s := s) i.castSucc))
    (hQ.trans (CompositionSeries.head_le (s := s) i.succ))).mpr (s.step i)

@[simp] theorem ChiefSeries.mapQuotient_head (s : ChiefSeries K) (Q : NormalNode K)
    (hQ : Q ≤ s.head) : (s.mapQuotient Q hQ).head = quotientImage Q s.head := rfl

@[simp] theorem ChiefSeries.mapQuotient_last (s : ChiefSeries K) (Q : NormalNode K)
    (hQ : Q ≤ s.head) : (s.mapQuotient Q hQ).last = quotientImage Q s.last := rfl

@[simp] theorem ChiefSeries.mapQuotient_noncentralTwoCount
    (s : ChiefSeries K) (Q : NormalNode K) (hQ : Q ≤ s.head) :
    (s.mapQuotient Q hQ).noncentralTwoCount = s.noncentralTwoCount := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun i => quotient_isNoncentralTwo_iff Q
    (s i.castSucc) (s i.succ) (hQ.trans (CompositionSeries.head_le (s := s) i.castSucc)))

/-- Every complete series has a quotient series with exactly the same
noncentral binary count when the kernel is central. -/
theorem ChiefSeries.exists_quotient_of_central [Finite K]
    (s : ChiefSeries K) (h0 : s.head = ⊥) (h1 : s.last = ⊤)
    (Q : NormalNode K) (hcentral : Q.val ≤ center K) :
    ∃ t : ChiefSeries (K ⧸ Q.val), t.head = ⊥ ∧ t.last = ⊤ ∧
      s.noncentralTwoCount = t.noncentralTwoCount := by
  obtain ⟨a, ha0, ha1⟩ := exists_chiefSeries (⊥ : NormalNode K) Q bot_le
  obtain ⟨b, hb0, hb1⟩ := exists_chiefSeries Q (⊤ : NormalNode K) le_top
  have hab : a.last = b.head := ha1.trans hb0.symm
  have ha : a.noncentralTwoCount = 0 := by
    apply a.noncentralTwoCount_eq_zero_of_central
    rw [ha0, ha1, isCentral_iff_commutator_le]
    change ⁅(⊤ : Subgroup K), Q.val⁆ ≤ ⊥
    rw [commutator_le]
    intro x _ y hy
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact mem_center_iff.mp (hcentral hy) x
  refine ⟨b.mapQuotient Q hb0.ge, ?_, ?_, ?_⟩
  · rw [ChiefSeries.mapQuotient_head, hb0]
    apply Subtype.ext
    change Q.val.map (QuotientGroup.mk' Q.val) = ⊥
    apply le_bot_iff.mp
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mpr hx
  · rw [ChiefSeries.mapQuotient_last, hb1]
    apply Subtype.ext
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  · rw [ChiefSeries.mapQuotient_noncentralTwoCount]
    calc
      s.noncentralTwoCount = ChiefSeries.noncentralTwoCount (a.smash b hab) :=
        s.noncentralTwoCount_eq _
          (h0.trans ((RelSeries.head_smash hab).trans ha0).symm)
          (h1.trans ((RelSeries.last_smash hab).trans hb1).symm)
      _ = b.noncentralTwoCount := by rw [ChiefSeries.noncentralTwoCount_smash, ha, zero_add]

/-- A central surjection preserves the number of noncentral binary chief
factors in arbitrary complete chief series, with literal quotient actions. -/
theorem ChiefSeries.noncentralTwoCount_eq_of_central_surjective [Finite K]
    (f : K →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center K)
    (s : ChiefSeries K) (t : ChiefSeries H)
    (hs0 : s.head = ⊥) (hs1 : s.last = ⊤)
    (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) :
    s.noncentralTwoCount = t.noncentralTwoCount := by
  obtain ⟨r, hr0, hr1, hsr⟩ := s.exists_quotient_of_central hs0 hs1 ⟨f.ker, inferInstanceAs f.ker.Normal⟩ hc
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  obtain ⟨hu0, hu1⟩ := r.mapActor_complete e hr0 hr1
  calc
    s.noncentralTwoCount = r.noncentralTwoCount := hsr
    _ = (r.mapActor e).noncentralTwoCount := (r.mapActor_noncentralTwoCount e).symm
    _ = t.noncentralTwoCount := (r.mapActor e).noncentralTwoCount_eq t
      (hu0.trans ht0.symm) (hu1.trans ht1.symm)

end NoncentralChiefRefinement
