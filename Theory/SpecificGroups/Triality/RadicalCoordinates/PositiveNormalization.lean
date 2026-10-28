module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.FixedPoints

/-!
# Positive normalization of the triality radical root products

Conjugating one positive root curve by another introduces at most the curve
on their sum. Every such sum is outside both Levi subsystems. The proved
Geck exchange identities therefore show that the full positive subgroup
normalizes either radical root product.

For the whole parabolic, this reduces relative normality to the actions of
the negative Levi roots and the coroot words. These remaining actions are
explicit hypotheses here, not asserted matrix identities.

Source: GLS3 §§2.4, 2.6, especially Definition 2.6.4 and Theorem 2.6.5
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.PositiveCoordinates
namespace Triality.Standard.RadicalCoordinates
open Parabolics

/-- Positive conjugation preserves the source radical support. -/
theorem positive_curve_conj_mem_rootSubgroup (P : Parameters) (hp : P.prime = 2)
    (a : Node) (i j : Fin 12) (hj : rootSupport a j) (s t : ExtensionField P) :
    curve P i s * curve P j t * (curve P i s)⁻¹ ∈ rootSubgroup P a := by
  have hsum : SumExchange P := by
    obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
    exact sumExchange_binary n hn
  have hcomm : NonsumCommute P := by
    obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
    exact nonsumCommute_binary n hn
  by_cases hij : i = j
  · subst j
    have hc : Commute (curve P i s) (curve P i t) := by
      change curve P i s * curve P i t = curve P i t * curve P i s
      exact (curve_add P i s t).symm.trans
        ((congrArg (curve P i) (add_comm s t)).trans (curve_add P i t s))
    rw [hc.mul_inv_cancel]
    exact curve_mem_rootSubgroup P a i hj t
  · by_cases h : ∃ k : Fin 12, (typeDRootPairing 2).root (rootIndex k) =
        (typeDRootPairing 2).root (rootIndex j) +
          (typeDRootPairing 2).root (rootIndex i)
    · obtain ⟨k, hk⟩ := h
      have he : curve P j t * (curve P i s)⁻¹ =
          (curve P i s)⁻¹ * curve P j t * curve P k (t * -s) := by
        simpa only [← curve_inv] using hsum j i k hk t (-s)
      have hconj : curve P i s * curve P j t * (curve P i s)⁻¹ =
          curve P j t * curve P k (t * -s) := by
        rw [mul_assoc, he]
        simp only [← mul_assoc, mul_inv_cancel, one_mul]
      rw [hconj]
      exact (rootSubgroup P a).mul_mem (curve_mem_rootSubgroup P a j hj t)
        (curve_mem_rootSubgroup P a k (rootSupport_of_sum a hk) _)
    · have hc : Commute (curve P j t) (curve P i s) := hcomm j i (Ne.symm hij) h t s
      have he : curve P i s * curve P j t * (curve P i s)⁻¹ = curve P j t :=
        (congrArg (fun z : SplitGroup P => z * (curve P i s)⁻¹) hc.eq.symm).trans
          (mul_inv_cancel_right _ _)
      rw [he]
      exact curve_mem_rootSubgroup P a j hj t

/-- A generator test for normalizing the radical root subgroup. Finiteness
turns preservation by conjugation into equality. -/
theorem mem_rootSubgroup_normalizer_of_curve_conj (P : Parameters) (a : Node)
    (g : SplitGroup P)
    (h : ∀ j, rootSupport a j → ∀ t,
      g * curve P j t * g⁻¹ ∈ rootSubgroup P a) :
    g ∈ Subgroup.normalizer (rootSubgroup P a) := by
  apply Subgroup.mem_normalizer_fintype
  have hle : rootSubgroup P a ≤ (rootSubgroup P a).comap (MulAut.conj g).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨j, hj, t, rfl⟩
    exact h j hj t
  exact fun x hx => hle hx

theorem positiveSubgroup_le_rootSubgroup_normalizer (P : Parameters)
    (hp : P.prime = 2) (a : Node) :
    positiveSubgroup P ≤ Subgroup.normalizer (rootSubgroup P a) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i, s, rfl⟩
  rw [← curve_simple]
  apply mem_rootSubgroup_normalizer_of_curve_conj
  exact fun j hj t => positive_curve_conj_mem_rootSubgroup P hp a _ j hj s t

/-- The two outstanding kinds of generators suffice for relative parabolic
normality; all positive generators have already been handled unconditionally. -/
theorem rootSubgroup_normal_of_generator_actions (P : Parameters)
    (hp : P.prime = 2) (a : Node)
    (hneg : ∀ i ∈ a.support, ∀ s, ∀ j, rootSupport a j → ∀ t,
      negativeRoot P i s * curve P j t * (negativeRoot P i s)⁻¹ ∈ rootSubgroup P a)
    (htor : ∀ i s, ∀ j, rootSupport a j → ∀ t,
      torusWord P i s * curve P j t * (torusWord P i s)⁻¹ ∈ rootSubgroup P a) :
    ((rootSubgroup P a).subgroupOf (splitParabolic P a)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((rootSubgroup_le_splitRadical P hp a).trans
      (splitRadical_le_splitParabolic P a))).mpr
  apply sup_le
  · apply sup_le (positiveSubgroup_le_rootSubgroup_normalizer P hp a)
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, s, rfl⟩
    exact mem_rootSubgroup_normalizer_of_curve_conj P a _ (htor i s)
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, hi, s, rfl⟩
    exact mem_rootSubgroup_normalizer_of_curve_conj P a _ (hneg i hi s)

end Triality.Standard.RadicalCoordinates
