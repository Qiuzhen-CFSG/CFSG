module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.Structure
public import CFSG.Quasithin.Defs
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ThreeRank
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.PSL3Four.ThreeRank

/-!
# Model inputs for the three-local terminal deductions

The J₂ carrier has trivial center because its literal permutation extension
acts faithfully by conjugation. M₂₃ inherits an elementary nine from its
actual M₂₂ point stabilizer. Together with the matrix witness in PSL₃(4),
these establish the rank hypotheses from actual model equivalences.

Source: Aschbacher–Smith, 13.6.27, printed pp.934–935; A.3.18, pp.51–52.
No assertion about a family label substitutes for a group equivalence.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure

/-- Faithfulness of the concrete extension makes the J₂ carrier centerless. -/
theorem j2_center_eq_bot : center Sporadic.LeechRelated.J2.Carrier = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  change x = 1
  have hconj : MulAut.conj x = 1 := by
    apply MulEquiv.ext
    intro y
    change x * y * x⁻¹ = y
    rw [← (mem_center_iff.mp hx y), mul_inv_cancel_right]
  have he := Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionAction_injective
    (show Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionAction
      (Sporadic.LeechRelated.J2.ExceptionalParabolics.intoExtension x) =
      Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionAction 1 by
      rw [map_one, Sporadic.LeechRelated.J2.ExceptionalParabolics.extensionAction_inner, hconj])
  exact (Subgroup.inclusion_injective (show Sporadic.LeechRelated.J2.generated ≤
    Sporadic.LeechRelated.J2.ExceptionalParabolics.extension from le_sup_left)) he

/-- The actual M₂₂ point stabilizer supplies rank two in M₂₃. -/
theorem m23_three_rank_ge_two : 2 ≤ primeRank 3 Sporadic.Mathieu.M23 := by
  have he := primeRank_congr 3 Sporadic.Mathieu.m23EquivM22PointStabilizer
  rw [Sporadic.Mathieu.m22_primeRank_three] at he
  exact he.le.trans (primeRank_subgroup_le 3 _)

private theorem center_eq_bot_of_perfect_simple {A : Type*} [Group A]
    [IsSimpleGroup A] [Group.IsPerfect A] : center A = ⊥ := by
  rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp ht)).elim

private theorem center_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have he : e x ∈ center B := (centerCongr e ⟨x, hx⟩).property
  rw [hz, mem_bot] at he
  exact e.map_eq_one_iff.mp he

variable {H : Type*} [Group H] [Finite H] {T K : Subgroup H}

omit [Finite H] in
/-- Each of the three actual candidate quotients is centerless. -/
theorem candidate_center_eq_bot (hK : K.IsCComponent) (h : Candidate T K) :
    center (K ⧸ pCore 2 K) = ⊥ := by
  let _ := hK.perfect
  rcases h with h | h | ⟨e, _⟩
  · exact center_transport (Classical.choice h) j2_center_eq_bot
  · let e := Classical.choice h
    let _ := Sporadic.Mathieu.m23_isSimpleGroup
    let _ : Group.IsPerfect Sporadic.Mathieu.M23 := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact center_transport e center_eq_bot_of_perfect_simple
  · let _ : IsSimpleGroup L3Four := Atlas.psl_simple_high_rank 3 (by decide)
    let _ : Group.IsPerfect L3Four := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact center_transport e center_eq_bot_of_perfect_simple

/-- The three actual models all contain an elementary nine. -/
theorem candidate_three_rank_ge_two (h : Candidate T K) :
    2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
  rcases h with h | h | ⟨e, _⟩
  · rw [primeRank_congr 3 (Classical.choice h)]
    exact Sporadic.LeechRelated.J2.three_rank_ge_two
  · rw [primeRank_congr 3 (Classical.choice h)]
    exact m23_three_rank_ge_two
  · rw [primeRank_congr 3 e]
    exact Matrix.PSL3Four.ThreeRank.three_rank_ge_two

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.ThreeStructure
