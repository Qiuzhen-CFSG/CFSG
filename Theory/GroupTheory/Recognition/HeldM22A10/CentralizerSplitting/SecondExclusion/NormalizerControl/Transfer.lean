module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.SecondExclusion.NormalizerControl.Geometry

/-!
# Conditional transfer obstruction for the exceptional action

The block kernel has index two in the actual local model. Its involutions are
squares or conjugates of one marked outer involution. If the latter is fused
to a square by an ambient exceptional action, transfer forces the marked
outside involution to be an ambient square. A separate ambient normalizer
argument must rule this out; no unconditional normalizer control is asserted.

This is part of the splitting problem of Huppert--Blackburn III, XII.1.18(b),
printed p.314. The transfer calculation is Thompson's involution transfer,
as in `Theory.GroupTheory.InvolutionTransfer`, applied to an odd-index overgroup
of the Sylow subgroup.
-/

namespace Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl
open Subgroup NonsplitModels

private theorem exists_isConj_ker_of_odd_index
    {G A : Type*} [Group G] [CommGroup A] [Finite G] [Finite A]
    (S : Subgroup G) (hodd : S.index % 2 = 1)
    (hno : ∀ K : Subgroup G, K.Normal → K.index ≠ 2)
    (character : S →* A) (hcard : Nat.card A = 2)
    (element : S) (horder : orderOf element = 2) :
    ∃ other : S, IsConj (element : G) (other : G) ∧ character other = 1 := by
  classical
  by_contra! hnot
  have hnontrivial : character element ≠ 1 := hnot element (IsConj.refl _)
  have heq (left right : A) (hleft : left ≠ 1) (hright : right ≠ 1) : left = right := by
    obtain ⟨unique, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
    exact (hunique left hleft).trans (hunique right hright).symm
  have hrespect (power : ℕ) (other : S)
      (hconj : IsConj (((element ^ power) : S) : G) (other : G)) :
      character other = character (element ^ power) := by
    have hreduce : element ^ power = element ^ (power % 2) := by
      simpa only [horder] using (pow_mod_orderOf element power).symm
    rw [hreduce] at hconj ⊢
    have hbound : power % 2 < 2 := Nat.mod_lt _ (by decide)
    generalize hremainder : power % 2 = remainder at hconj ⊢ hbound
    interval_cases remainder
    · have hother : other = 1 := Subtype.coe_injective
        (isConj_one_right.mp (by simpa using hconj))
      simp [hother]
    · simp only [pow_one] at hconj ⊢
      exact heq _ _ (hnot other hconj) hnontrivial
  have htransfer :=
    character.transfer_apply_eq_pow_of_conjugate_powers element hrespect
  have hindex : character.transfer.ker.index = 1 := by
    have hdiv : character.transfer.ker.index ∣ 2 := by
      rw [Subgroup.index_ker]
      have hdiv := Subgroup.card_subgroup_dvd_card character.transfer.range
      rwa [hcard] at hdiv
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hdiv with hone | htwo
    · exact hone
    · exact (hno _ inferInstance htwo).elim
  have htrivial : character.transfer (element : G) = 1 := by
    change (element : G) ∈ character.transfer.ker
    rw [Subgroup.index_eq_one.mp hindex]
    trivial
  have hpower : character element ^ (S : Subgroup G).index = character element := by
    have h := pow_mod_natCard (character element) (S : Subgroup G).index
    simpa only [hcard, hodd, pow_one] using h.symm
  exact hnontrivial (hpower.symm.trans (htransfer.symm.trans htrivial))


private theorem square_of_isConj {G : Type*} [Group G] {x y : G}
    (h : IsConj x y) (hy : ∃ r : G, r ^ 2 = y) : ∃ r : G, r ^ 2 = x := by
  obtain ⟨r, hr⟩ := hy
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  refine ⟨(MulAut.conj g).symm r, ?_⟩
  apply (MulAut.conj g).injective
  rw [map_pow, MulEquiv.apply_symm_apply, hr]
  exact hg.symm

/-- Exceptional fusion and absence of an outside square contradict simplicity.
Both extra premises remain obligations of the normalizer-control assembly. -/
public theorem false_of_outer_fusion_of_no_outside_square
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (D : LocalData G) (e : D.centralizer ≃* Second)
    (hfusion : IsConj (embedding D e outerPoint) (embedding D e squarePoint))
    (hnosquare : ¬ ∃ r : G, r ^ 2 = embedding D e outsidePoint) : False := by
  let : blockKernel.Normal := blockKernel.normal_of_index_eq_two blockKernel_index
  have hcard : Nat.card (Second ⧸ blockKernel) = 2 := blockKernel_index
  let : IsCyclic (Second ⧸ blockKernel) := isCyclic_of_prime_card hcard
  let : CommGroup (Second ⧸ blockKernel) := IsCyclic.commGroup
  let χ : D.centralizer →* Second ⧸ blockKernel :=
    (QuotientGroup.mk' blockKernel).comp e.toMonoidHom
  have hodd : D.centralizer.index % 2 = 1 := by
    have hdiv := index_dvd_of_le D.sylow_le_centralizer
    have hnot : ¬ 2 ∣ D.centralizer.index := fun h => D.sylow.not_dvd_index (h.trans hdiv)
    omega
  have horder : orderOf (e.symm outsidePoint) = 2 :=
    (e.symm.orderOf_eq outsidePoint).trans outsidePoint_order
  obtain ⟨y, hxy, hy⟩ := exists_isConj_ker_of_odd_index D.centralizer hodd
    (D.no_normal_index_two) χ hcard (e.symm outsidePoint) horder
  have hyK : e y ∈ blockKernel := (QuotientGroup.eq_one_iff (N := blockKernel) (x := e y)).mp hy
  have hyorder : orderOf (e y) = 2 := by
    obtain ⟨a, ha⟩ := isConj_iff.mp hxy
    have he : orderOf (y : G) = orderOf ((e.symm outsidePoint : D.centralizer) : G) := by
      rw [← ha]
      exact (MulAut.conj a).orderOf_eq _
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, horder] at he
    exact (e.orderOf_eq y).trans he
  have hy2 : (e y) ^ 2 = 1 := by simpa only [hyorder] using pow_orderOf_eq_one (e y)
  have hyembed : embedding D e (e y) = (y : G) := by
    change (e.symm (e y) : G) = (y : G)
    rw [e.symm_apply_apply]
  have hysquare : ∃ r : G, r ^ 2 = (y : G) := by
    rcases blockKernel_square_or_conjugate (e y) hyK hy2 with hs | hc
    · obtain ⟨r, hr⟩ := hs
      exact ⟨embedding D e r, by rw [← map_pow, hr, hyembed]⟩
    · have hconj := (embedding D e).map_isConj hc
      rw [hyembed] at hconj
      apply square_of_isConj (hconj.symm.trans hfusion)
      exact ⟨embedding D e (Model.element 163), by rw [← map_pow, squarePoint_root]⟩
  apply hnosquare
  exact square_of_isConj hxy hysquare

end Theory.GroupTheory.HeldM22A10.SecondExclusion.NormalizerControl
