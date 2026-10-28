module

public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.PGroup

/-!
# Replacing a conjugator modulo a p-group quotient

Let `N` be a normal subgroup of a finite group `K` with p-group quotient,
where `p` is prime. If `A` and its conjugate by `x` generate `K`, an element
of `N` induces the same conjugate of `A` as `x`.

The image of `A` in the quotient is the whole quotient: otherwise it lies
in a maximal proper subgroup, which is normal by the normalizer condition
for finite nilpotent groups. Its pullback contains both generating
conjugates, a contradiction. Choose `a ∈ A` with the same quotient image as
`x`; then `x / a ∈ N`, and conjugation by `a` fixes `A`.

This independent finite-group argument supplies the residual-conjugator
replacement used in Stellmacher (9.3)(i), Journal of Algebra 190 (1997),
with the two-residual of the generated subgroup as `N`. No residual or
campaign-specific hypotheses are needed here.
-/

namespace Subgroup

public theorem exists_normal_conjugator_of_isPGroup_quotient
    {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (A N : Subgroup K) [N.Normal] (hquot : IsPGroup p (K ⧸ N))
    (x : K) (hgen : A ⊔ A.conjBy x = ⊤) :
    ∃ y : K, y ∈ N ∧ A.conjBy y = A.conjBy x := by
  classical
  let quotientMap := QuotientGroup.mk' N
  have himage : A.map quotientMap = ⊤ := by
    by_contra hproper
    obtain ⟨maximalSubgroup, hmaximal, himage_le⟩ :=
      (eq_top_or_exists_le_coatom (A.map quotientMap)).resolve_left hproper
    let : Group.IsNilpotent (K ⧸ N) := hquot.isNilpotent
    let : maximalSubgroup.Normal := Subgroup.NormalizerCondition.normal_of_coatom
      maximalSubgroup Group.normalizerCondition_of_isNilpotent hmaximal
    have hA : A ≤ maximalSubgroup.comap quotientMap := by
      intro actor hactor
      exact himage_le (mem_map_of_mem quotientMap hactor)
    have hconj : A.conjBy x ≤ maximalSubgroup.comap quotientMap := by
      rintro element ⟨actor, hactor, rfl⟩
      exact (inferInstance : (maximalSubgroup.comap quotientMap).Normal).conj_mem
        actor (hA hactor) x
    have hfull : maximalSubgroup.comap quotientMap = ⊤ := by
      apply top_le_iff.mp
      rw [← hgen]
      exact sup_le hA hconj
    apply hmaximal.ne_top
    apply top_le_iff.mp
    intro element _
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective N element
    exact (show lift ∈ maximalSubgroup.comap quotientMap from hfull ▸ mem_top lift)
  obtain ⟨actor, hactor, hactorImage⟩ :=
    (show quotientMap x ∈ A.map quotientMap from himage ▸ mem_top _)
  refine ⟨x / actor, ?_, ?_⟩
  · exact QuotientGroup.eq_iff_div_mem.mp hactorImage.symm
  · ext element
    constructor
    · rintro ⟨member, hmember, rfl⟩
      refine ⟨actor⁻¹ * member * actor,
        A.mul_mem (A.mul_mem (A.inv_mem hactor) hmember) hactor, ?_⟩
      simp [MulAut.conj_apply, div_eq_mul_inv, mul_assoc]
    · rintro ⟨member, hmember, rfl⟩
      refine ⟨actor * member * actor⁻¹,
        A.mul_mem (A.mul_mem hactor hmember) (A.inv_mem hactor), ?_⟩
      simp [MulAut.conj_apply, div_eq_mul_inv, mul_assoc]

end Subgroup
