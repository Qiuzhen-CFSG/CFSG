module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Checks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Seeds
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.PointChecks
public import Theory.GroupAction.GeneratorStabilizerReduction

/-!
# Assembly of the second two model stabilizer inclusions

The finite right-coset tables have checked inverse columns, root fibers and
literal tree-word equations. Six additional edges are exactly the given
next-stage generators. Induction on a group word tracks both a coset
representative and the inverse image of the base label, so that a fixed
base label forces the identity representative.

Two inputs remain: comparisons of the literal model generators with the
label transitions, and the nontree Schreier memberships in the literal next
groups. The theorem here is conditional on precisely those inputs. It does
not assert `second_two_reductions` before they have been discharged.
Source: ATLAS F24G1-p306936B0 and GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
open StagesTwoFour

private theorem reduction_from_tables (ha : InverseAction) (he : NonTreeEdges)
    (i : Fin 2) (g : Ambient) (hg : g ∈ stage (i.natAdd 2).castSucc)
    (hfix : g (point (i.natAdd 2)) = point (i.natAdd 2)) :
    g ∈ stage (i.natAdd 2).succ := by
  let H := stage (i.natAdd 2).succ
  have step (a : Fin 2) (j : Fin (size i)) :
      ∃ k : H, representative i j * gen i a = k.val * representative i (next i a j) := by
    refine ⟨⟨schreier i a j, all_edges_of_nonTree he i a j⟩, ?_⟩
    simp only [schreier, mul_assoc, inv_mul_cancel, mul_one]
  have invstep (a : Fin 2) (j : Fin (size i)) :
      ∃ k : H, representative i j * (gen i a)⁻¹ = k.val * representative i (prev i a j) := by
    obtain ⟨k, hk⟩ := step a (prev i a j)
    rw [next_prev] at hk
    refine ⟨k⁻¹, ?_⟩
    have hh := congrArg (fun x : Ambient => k.val⁻¹ * x * (gen i a)⁻¹) hk
    simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one,
      Subgroup.coe_inv] using hh.symm
  have forward (a : Fin 2) (j : Fin (size i)) :
      gen i a (label i j) = label i (prev i a j) := by
    have hh := congrArg (gen i a) (ha i a (prev i a j))
    simpa only [next_prev, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using hh.symm
  have hgen : g ∈ Subgroup.closure (Set.range (gen i)) := by
    simpa only [gen, stage_generated] using hg
  have decomp : ∃ k : H, ∃ j : Fin (size i),
      g = k.val * representative i j ∧ g⁻¹ (label i (root i)) = label i j := by
    clear hg hfix
    induction hgen using Subgroup.closure_induction_right with
    | one =>
      exact ⟨1, root i, by simp [root_representative]⟩
    | mul_right x _ y hy ih =>
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨k, j, hx, hlabel⟩ := ih
      obtain ⟨k', hstep⟩ := step a j
      refine ⟨k * k', next i a j, ?_, ?_⟩
      · rw [hx, mul_assoc, hstep, ← mul_assoc]
        rfl
      · simpa only [mul_inv_rev, Equiv.Perm.mul_apply, hlabel] using ha i a j
    | mul_inv_cancel x _ y hy ih =>
      obtain ⟨a, rfl⟩ := hy
      obtain ⟨k, j, hx, hlabel⟩ := ih
      obtain ⟨k', hstep⟩ := invstep a j
      refine ⟨k * k', prev i a j, ?_, ?_⟩
      · rw [hx, mul_assoc, hstep, ← mul_assoc]
        rfl
      · simpa only [mul_inv_rev, inv_inv, Equiv.Perm.mul_apply, hlabel] using forward a j
  obtain ⟨k, j, hk, hj⟩ := decomp
  rw [point_eq_root_label] at hfix
  have hi : g⁻¹ (label i (root i)) = label i (root i) := by
    apply g.injective
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using hfix.symm
  have hr : j = root i := root_fiber i j (hj.symm.trans hi)
  rw [hr, root_representative, mul_one] at hk
  rw [hk]
  exact k.property

/-- The literal finite comparisons and nontree memberships suffice for both
requested inclusions. Final assembly must prove both premises. -/
theorem second_two_reductions_of_certificates (ha : InverseAction) (he : NonTreeEdges) :
    ∀ i : Fin 2, ∀ g : Equiv.Perm (Fin 306936),
      g ∈ stage (i.natAdd 2).castSucc →
      g (point (i.natAdd 2)) = point (i.natAdd 2) →
      g ∈ stage (i.natAdd 2).succ :=
  reduction_from_tables ha he

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
