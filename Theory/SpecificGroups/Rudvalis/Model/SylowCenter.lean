module

public import Theory.SpecificGroups.Rudvalis.Model.SylowCenter.Certificate
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.Sylow.NormalFormCoverage
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Sylow


/-!
# Centers of Rudvalis Sylow two-subgroups

The existing word-defined max4 candidate has order 2^14, and the certified
ambient two-part bound makes it a Sylow subgroup. Its complete binary normal
forms reduce centrality to a finite calculation: commutation with three actual
generators on two points permits only normal forms 0 and 6144. Thus its center
injects into a two-element type. Sylow conjugacy transports the bound to every
Sylow two-subgroup of the original degree-4060 Rudvalis model.

The result is unconditional, including no simplicity or perfectness premise.
Source: GLS3 Table 5.3r, printed p.279, and Aschbacher–Smith, 1.1.5(3)(f),
pp.501–503, as used in the proof of 13.6.6, printed p.927. The original ATLAS
words, permutation action and attribution are retained in the imported
SylowOvergroups.RadicalCoverage.Sylow modules.
-/

public section

open Subgroup
namespace Rudvalis.SylowCenter
open SylowOvergroups.RadicalCoverage.SylowCertificate
open SylowOvergroups.RadicalCoverage.SylowCertificate.LocalOrder

private theorem central_normal_form (z : center candidate) :
    (z.val : Model) = candidateNormalForm 0 ∨
      (z.val : Model) = candidateNormalForm 6144 := by
  obtain ⟨n, hn⟩ := exists_candidateNormalForm z.val.property
  have hcomm (i : Fin 14) (x : Fin 4060) :
      normalMap n (generatorMap i x) = generatorMap i (normalMap n x) := by
    have hi : candidateGenerator i ∈ candidate :=
      subset_closure (Set.mem_range_self i)
    have hc := congrArg (fun y : candidate => (y : Model))
      (mem_center_iff.mp z.property ⟨candidateGenerator i, hi⟩)
    change candidateGenerator i * (z.val : Model) =
      (z.val : Model) * candidateGenerator i at hc
    rw [← hn] at hc
    have hp := congrArg (fun g : Model => g • x) hc.symm
    simpa only [mul_smul, normal_smul, generator_smul] using hp
  rcases Certificate.index_eq_of_point_commutation n hcomm with h | h
  · have hn0 : n = 0 := Fin.ext h
    exact Or.inl (hn.symm.trans (congrArg candidateNormalForm hn0))
  · have hn1 : n = 6144 := Fin.ext h
    exact Or.inr (hn.symm.trans (congrArg candidateNormalForm hn1))

/-- The center of the literal word-defined candidate has at most two elements. -/
theorem candidate_center_card_le_two : Nat.card (center candidate) ≤ 2 := by
  classical
  let f : center candidate → Bool := fun z => decide ((z.val : Model) = candidateNormalForm 0)
  have hf : Function.Injective f := by
    intro x y h
    have he : (x.val : Model) = candidateNormalForm 0 ↔
        (y.val : Model) = candidateNormalForm 0 := decide_eq_decide.mp h
    apply Subtype.ext
    apply Subtype.ext
    rcases central_normal_form x with hx | hx
    · exact hx.trans (he.mp hx).symm
    · rcases central_normal_form y with hy | hy
      · exact (he.mpr hy).trans hy.symm
      · exact hx.trans hy.symm
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using
    Nat.card_le_card_of_injective f hf

private theorem candidate_odd_index : ¬ 2 ∣ candidate.index := by
  intro h
  apply not_two_pow_fifteen_dvd_card_model
  rw [← candidate.card_mul_index, candidate_card]
  exact Nat.mul_dvd_mul_left 16384 h

private noncomputable def candidateSylow : Sylow 2 Model :=
  candidate_isTwoGroup.toSylow candidate_odd_index

/-- Every Sylow two-subgroup of the original Rudvalis model has center of order at most two. -/
theorem sylow_center_card_le_two (P : Sylow 2 Model) : Nat.card (center P) ≤ 2 := by
  rw [Nat.card_congr (centerCongr (P.equiv candidateSylow)).toEquiv]
  exact candidate_center_card_le_two

end Rudvalis.SylowCenter
