module
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.FirstTwoPerfect
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# A noncentral two-core in the first two binary node residuals

For dimension at least four, the root from coordinate three into coordinate
zero belongs to the normal two-radical of the three-space parabolic and to
the first node residual. The opposite root on coordinates zero and one lies
in the pair and does not commute with it. Thus the actual first-pair group
has a noncentral two-core.

This is the upper moved layer used in Aschbacher--Smith 15.1.29,
printed pp.1103--1104.
-/

public section
open Subgroup Theory.GroupTheory
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
namespace BinaryLinear.OrderedResidualConjugators

private theorem root_transvection {m : ℕ} (b : Basis m)
    (r s : Fin (m+1)) (hrs : r ≠ s) :
    root b r s hrs = transvection (b r) (b.coord s) (by simp [hrs]) := by
  apply b.ext'
  intro j
  rw [root_basis]
  change (if j = s then b j + b r else b j) = b j + b.coord s (b j) • b r
  by_cases hj : j = s <;> simp [hj,Module.Basis.coord_apply]

private theorem root_in_radical {m : ℕ} (b : Basis m) (i : Fin m)
    (r s : Fin (m+1)) (hrs : r ≠ s) (hr : r.val ≤ i.val) (hs : i.val < s.val) :
    root b r s hrs ∈ radical (cutSpace b i) := by
  have hcoord : ∀ v ∈ cutSpace b i, b.coord s v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j,hj,rfl⟩ := hv
      have hjs : j ≠ s := by intro he; subst j; exact (Nat.not_le_of_gt hs) hj
      simp [Module.Basis.coord_apply,hjs]
    | zero => exact map_zero _
    | add v w hv hw ihv ihw => simp only [map_add,ihv,ihw,add_zero]
    | smul c v hv ih => simp only [map_smul,ih,smul_zero]
  rw [root_transvection]
  constructor
  · intro v hv
    change v + b.coord s v • b r = v
    rw [hcoord v hv,zero_smul,add_zero]
  · intro v
    change v + b.coord s v • b r - v ∈ cutSpace b i
    rw [add_sub_cancel_left]
    exact (cutSpace b i).smul_mem _ ((basis_mem_cutSpace b i r).mpr hr)

private theorem noncommute_of_action_chain {n : ℕ}
    (x y : LinearGroup n) (u r s : Fin n → ZMod 2)
    (hx : x u = u + r) (hyu : y u = u) (hyr : y r = r + s)
    (hs : s ≠ 0) : ¬ Commute y x := by
  intro hc
  have hh := congrArg (fun g : LinearGroup n => g u) hc.eq
  change y (x u) = x (y u) at hh
  rw [hx,hyu,map_add,hyu,hyr,hx] at hh
  exact hs (add_eq_left.mp (add_left_cancel hh))

private theorem root_not_commute {m : ℕ} (b : Basis m)
    (r s u : Fin (m+1)) (hrs : r ≠ s) (hru : r ≠ u) :
    ¬ Commute (root b s r hrs.symm) (root b r u hru) := by
  apply noncommute_of_action_chain _ _ (b u) (b r) (b s)
  · exact (root_basis b r u hru u).trans (if_pos rfl)
  · exact (root_basis b s r hrs.symm u).trans (if_neg hru.symm)
  · exact (root_basis b s r hrs.symm r).trans (if_pos rfl)
  · exact b.ne_zero s

/-- The first-pair image has a genuinely noncentral two-core. The root
from the fourth coordinate into the first lies in its normal two-radical,
and fails to commute with the opposite root on the first two coordinates. -/
theorem first_two_core_not_central {m : ℕ} (hm : 3 ≤ m) (b : Basis m) :
    ¬ pCore 2 (nodeResidual b ⟨0,by omega⟩ ⊔ nodeResidual b ⟨1,by omega⟩ :
      Subgroup (LinearGroup (m+1))) ≤ center
      (nodeResidual b ⟨0,by omega⟩ ⊔ nodeResidual b ⟨1,by omega⟩ :
      Subgroup (LinearGroup (m+1))) := by
  let K := nodeResidual b ⟨0,by omega⟩ ⊔ nodeResidual b ⟨1,by omega⟩
  let W := cutSpace b ⟨2,by omega⟩
  let z : Fin (m+1) := ⟨0,by omega⟩
  let o : Fin (m+1) := ⟨1,by omega⟩
  let u : Fin (m+1) := ⟨3,by omega⟩
  have hzu : z ≠ u := by simp [z,u]
  have hoz : o ≠ z := by simp [o,z]
  let x := root b z u hzu
  let y := root b o z hoz
  have hxK : x ∈ K := mem_sup_left
    (incident_root_mem_nodeResidual b ⟨0,by omega⟩ _ _ _
      (Or.inr ⟨Or.inl rfl,by simp [u]⟩))
  have h01 : root b z o (by simp [z,o]) ∈ K := mem_sup_right
    (incident_root_mem_nodeResidual b ⟨1,by omega⟩ _ _ _
      (Or.inl ⟨by simp [z],Or.inl rfl⟩))
  have hyK : y ∈ K := by
    have hc : cubic b z o (by simp [z,o]) ∈ K :=
      mem_sup_left (cubic_mem_nodeResidual b ⟨0,by omega⟩)
    have hh := K.mul_mem (K.inv_mem h01) hc
    simpa only [cubic,inv_mul_cancel_left] using hh
  have hKP : K ≤ parabolic W := by
    apply sup_le
    · intro g hg
      have hh := map_subtype_le (pResidual 2 (minimalParabolic b ⟨0,by omega⟩)) hg
      exact (mem_cutStabilizer b _ _).mp hh ⟨2,by omega⟩ (by simp) 
    · intro g hg
      have hh := map_subtype_le (pResidual 2 (minimalParabolic b ⟨1,by omega⟩)) hg
      exact (mem_cutStabilizer b _ _).mp hh ⟨2,by omega⟩ (by simp)
  have hxR : x ∈ radical W := root_in_radical b ⟨2,by omega⟩ z u hzu
    (by simp [z]) (by simp [u])
  have hnorm : K ≤ normalizer ((K ⊓ radical W : Subgroup (LinearGroup (m+1))) : Set _) :=
    (le_inf K.le_normalizer (hKP.trans (parabolic_le_normalizer W))).trans
      inf_normalizer_le_normalizer_inf
  have hcore : K ⊓ radical W ≤ K.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((radical_two W).to_le inf_le_right) inf_le_left hnorm
  have hxcore : (⟨x,hxK⟩ : K) ∈ pCore 2 K := by
    obtain ⟨q,hq,he⟩ := hcore ⟨hxK,hxR⟩
    exact (Subtype.ext he : q = ⟨x,hxK⟩) ▸ hq
  intro hc
  have hxy : Commute y x := congrArg Subtype.val
    (mem_center_iff.mp (hc hxcore) ⟨y,hyK⟩)
  exact root_not_commute b z o u hoz.symm hzu hxy
end BinaryLinear.OrderedResidualConjugators
