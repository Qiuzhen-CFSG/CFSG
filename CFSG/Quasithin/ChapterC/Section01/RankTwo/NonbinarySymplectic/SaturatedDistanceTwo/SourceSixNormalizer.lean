module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceSixElement

/-!
# The normalizer step in MS93 (3.7)(6)

The first element supplied by `SourceSixElement` is followed in the source by
the normalizer argument on the coset `x Qₐ`.  This file records the literal
group-theoretic transport used there.  In particular, the element which moves
the opposite coset is still an explicit source premise; the lemma does not
select a critical pair by assuming its conclusion.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(6), printed p.876.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo

variable {G : Type*} [Group G]

/-- Equality of the two left cosets gives the quotient element used in the
normalizer calculation.  The orientation is the one used in the printed
argument: `x⁻¹ y ∈ Q` when `x Q = y Q`. -/
theorem source_six_coset_eq_iff
    (Q : Subgroup G) (x y : G) :
    x • (Q : Set G) = y • (Q : Set G) ↔ x⁻¹ * y ∈ Q := by
  constructor
  · intro h
    have hy : y ∈ x • (Q : Set G) := by
      rw [h]
      simpa using (Set.smul_mem_smul_set (a := y) Q.one_mem)
    exact Set.mem_smul_set_iff_inv_smul_mem.mp hy
  · intro h
    apply Set.Subset.antisymm
    · rintro _ ⟨q, hq, rfl⟩
      have h' : y⁻¹ * x ∈ Q := by
        simpa using Q.inv_mem h
      refine ⟨(y⁻¹ * x) * q, Q.mul_mem h' hq, ?_⟩
      simp only [smul_eq_mul]
      group
    · rintro _ ⟨q, hq, rfl⟩
      refine ⟨(x⁻¹ * y) * q, Q.mul_mem h hq, ?_⟩
      simp only [smul_eq_mul]
      group

/-- The conjugate of `x` stays in its coset whenever the conjugator lies in
the coset normalizer.  The second conjunct is the exact quotient element
used later to place the commutator in `Q`. -/
theorem source_six_conjugate_coset
    (Q : Subgroup G) (x g : G)
    (hg : g ∈ normalizer (x • (Q : Set G))) :
    MulAut.conj g x ∈ x • (Q : Set G) ∧
      x⁻¹ * MulAut.conj g x ∈ Q := by
  have hx : x ∈ x • (Q : Set G) := by
    simpa using (Set.smul_mem_smul_set (a := x) Q.one_mem)
  have hconj : MulAut.conj g x ∈ x • (Q : Set G) := by
    change g * x * g⁻¹ ∈ x • (Q : Set G)
    exact (mem_set_normalizer_iff.mp hg x).mp hx
  exact ⟨hconj, Set.mem_smul_set_iff_inv_smul_mem.mp hconj⟩

/-- The coset calculation places the commutator in the endpoint radical when
the endpoint element normalizes that radical.  This is the kernel inclusion
used in the source before the midpoint argument. -/
theorem source_six_commutator_mem
    (Q : Subgroup G) (x y : G)
    (hxQ : x ∈ normalizer (Q : Set G))
    (hxy : x⁻¹ * y ∈ Q) : ⁅x,y⁆ ∈ Q := by
  have hconj : x * (x⁻¹ * y) * x⁻¹ ∈ Q :=
    (mem_normalizer_iff.mp hxQ (x⁻¹ * y)).mp hxy
  have hinner :
      (x * (x⁻¹ * y) * x⁻¹) * (x⁻¹ * y)⁻¹ ∈ Q :=
    Q.mul_mem hconj (Q.inv_mem hxy)
  have houter : x * ((x * (x⁻¹ * y) * x⁻¹) * (x⁻¹ * y)⁻¹) * x⁻¹ ∈ Q :=
    (mem_normalizer_iff.mp hxQ _).mp hinner
  rw [commutatorElement_def]
  convert houter using 1
  · group

/-- The source's choice of a moving conjugator is just the failure of the
normalizer inclusion.  Keeping this as a separate lemma makes the missing
normalizer contradiction explicit to the eventual critical-pair assembly. -/
theorem source_six_exists_moving_conjugator
    (P S : Subgroup G) (hnot : ¬ P ≤ normalizer (S : Set G)) :
    ∃ g, g ∈ P ∧ g ∉ normalizer (S : Set G) := by
  exact Set.not_subset.mp hnot

/-- Combined source-(6) transport: after the source has shown that the
normalizer of `x Q` cannot normalize the opposite coset, choose a conjugator
and retain both its movement and the commutator-kernel conclusion. -/
theorem source_six_normalizer_step
    (Q S P : Subgroup G) (x : G)
    (hP : P = normalizer (x • (Q : Set G)))
    (hxQ : x ∈ normalizer (Q : Set G))
    (hnot : ¬ P ≤ normalizer (S : Set G)) :
    ∃ g, g ∈ P ∧ g ∉ normalizer (S : Set G) ∧
      x⁻¹ * MulAut.conj g x ∈ Q ∧
      ⁅x,MulAut.conj g x⁆ ∈ Q := by
  obtain ⟨g,hgP,hgS⟩ := source_six_exists_moving_conjugator P S hnot
  have hg : g ∈ normalizer (x • (Q : Set G)) := hP ▸ hgP
  obtain ⟨_,hcoset⟩ := source_six_conjugate_coset Q x g hg
  exact ⟨g,hgP,hgS,hcoset,source_six_commutator_mem Q x _ hxQ hcoset⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
