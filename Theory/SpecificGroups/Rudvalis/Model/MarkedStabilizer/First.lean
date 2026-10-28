module
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.Action
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.Orbits
/-!
# The first local subgroup in the actual Rudvalis action

The nine marked first-parabolic generators fix exactly the base point and
point2325. The full-Ree first parabolic normalizes their Atlas image, so its
inverse image fixes point2325. The already proved stabilizer orders turn this
inclusion into equality under the original full-model marking.

Source: Aschbacher–Smith, J.5.1 and J.5.4, pp.445–446.
-/

@[expose] public section
noncomputable section
namespace Rudvalis.MarkedStabilizer
open Subgroup MulAction Tits.ExceptionalParabolics
open OuterStabilizer.TitsEmbedding OuterStabilizer.TitsEmbedding.RelationCertificate

private theorem marked_generator_mem_first (i : Tits.ParrottGenerator) (hi : i≠.r8) :
    Tits.atlas1600ParrottAssignment i∈Tits.ExceptionalParabolics.first := by
  by_cases hr : i=.r1
  · subst i; exact reflection_mem_first
  apply sylow_le_first
  rw [S,Tits.atlas1600SylowTwoSubgroup_eq]
  apply Subgroup.subset_closure
  cases i <;> simp_all

private theorem atlas_first_fixes (x : Tits.Atlas1600Group)
    (hx : x∈Tits.ExceptionalParabolics.first) : atlasMap x • firstPoint=firstPoint := by
  let Q := (stabilizer Model firstPoint).comap atlasMap
  have hall (i : Tits.ParrottGenerator) (hi : i≠.r8) : Tits.atlas1600ParrottAssignment i∈Q := by
    change atlasMap (Tits.atlas1600ParrottAssignment i) • firstPoint=firstPoint
    rw [atlasMap_generator]
    have H := first_generators_fix i hi
    rw [permutation_eq] at H
    exact H
  have hle : Tits.ExceptionalParabolics.first≤Q := by
    unfold Tits.ExceptionalParabolics.first
    apply sup_le
    · rw [S,Tits.atlas1600SylowTwoSubgroup_eq]
      apply (closure_le _).mpr
      intro y hy
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hall .s8 (by decide)
      · exact hall .s7 (by decide)
      · exact hall .s6 (by decide)
      · exact hall .s5 (by decide)
      · exact hall .s4 (by decide)
      · exact hall .s3 (by decide)
      · exact hall .s2 (by decide)
      · exact hall .s1 (by decide)
    · apply (closure_le _).mpr
      rintro y (rfl : y=Tits.atlas1600ParrottAssignment .r1)
      exact hall .r1 (by decide)
  exact hle hx

private theorem first_action_preserves (g : ReeF4.Model 0) (hg : g∈FullRee.first)
    (x : Tits.Atlas1600Group) (hx : x∈Tits.ExceptionalParabolics.first) :
    FullRee.atlasAction g x∈Tits.ExceptionalParabolics.first := by
  have hmem : FullRee.atlasEmbedding (FullRee.atlasAction g x)∈
      Tits.ExceptionalParabolics.first.map FullRee.atlasEmbedding := by
    rw [FullRee.atlas_first_map]
    constructor
    · rw [FullRee.atlasAction_apply]
      exact FullRee.first.mul_mem
        (FullRee.first.mul_mem hg (FullRee.atlas_first_map_le ⟨x,hx,rfl⟩))
        (FullRee.first.inv_mem hg)
    · rw [← FullRee.atlasEmbedding_range]
      exact ⟨_,rfl⟩
  obtain ⟨y,hy,he⟩ := hmem
  exact FullRee.atlasEmbedding_injective he ▸ hy

private theorem fixes_firstPoint_of_fullEquiv_mem (g : pointStabilizer)
    (hg : fullEquiv g∈FullRee.first) : g • firstPoint=firstPoint := by
  have hcommon : ∀i : Tits.ParrottGenerator, i≠.r8 →
      permutation i (g • firstPoint)=g • firstPoint := by
    intro i hi
    let x := FullRee.atlasAction (fullEquiv g⁻¹) (Tits.atlas1600ParrottAssignment i)
    have hx : x∈Tits.ExceptionalParabolics.first := first_action_preserves _
      (by rw [map_inv]; exact FullRee.first.inv_mem hg) _ (marked_generator_mem_first i hi)
    have hfix := atlas_first_fixes x hx
    have he : atlasMap x=(g:Model)⁻¹*assignment i*(g:Model) := by
      dsimp [x]
      rw [fullEquiv_action,conjugation_apply,atlasMap_generator]
      rfl
    have H := congrArg (fun y : Fin 4060 => (g:Model) • y) hfix
    rw [he,mul_smul,mul_smul,smul_inv_smul] at H
    rw [permutation_eq]
    exact H
  rcases first_common_fixed _ hcommon with h0 | he
  · have hz : (g:Model) • (0 : Fin 4060)=0 := g.property
    have hx : firstPoint=0 := smul_left_cancel (g:Model) (h0.trans hz.symm)
    exact (by decide : firstPoint≠0) hx |>.elim
  · exact he

/-- The same full-model equivalence sends the literal first point stabilizer
onto the native Suzuki-side parabolic. -/
theorem first_marked :
    (stabilizer pointStabilizer firstPoint).map fullEquiv.toMonoidHom=FullRee.first := by
  apply (eq_of_le_of_card_ge ?_ ?_).symm
  · intro x hx
    refine ⟨fullEquiv.symm x,?_,fullEquiv.apply_symm_apply x⟩
    apply fixes_firstPoint_of_fullEquiv_mem
    simpa only [MulEquiv.apply_symm_apply] using hx
  · rw [card_map_of_injective fullEquiv.injective,first_stabilizer_card,FullRee.first_card]
end Rudvalis.MarkedStabilizer
