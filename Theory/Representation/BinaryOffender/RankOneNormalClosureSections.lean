module

public import Theory.Representation.BinaryOffender.RankOneNormalClosure
public import Theory.Representation.BinaryOffender.SectionLinear

/-!
# Rank-one normal-closure generation on literal sections

Displacement rank cannot increase on a subrepresentation followed by a
quotient. Thus every ambient conjugate of a rank-one involution still generates
a best offender on such a section of its literal normal closure. The section's
full offender subgroup is consequently the original normal closure itself.
Faithfulness is unnecessary for this generation statement.

This supplies the actual whole actor in the B.4 action list used by
Aschbacher–Smith, G.6.4, printed pp.345–346.
-/

public section

open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
theorem subquotient_displacement_rank_le (ρ : Representation (ZMod 2) G V)
    (W : Subrepresentation ρ) (C : Subrepresentation W.toRepresentation) (a : G) :
    Module.finrank (ZMod 2) (LinearMap.range (C.quotientRepresentation a - LinearMap.id)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) := by
  have hq := fixedCodim_quotient_add_subrepresentation_le W.toRepresentation C (zpowers a)
  have hw := fixedCodim_subrepresentation_le ρ W (zpowers a)
  simp only [fixedCodim_zpowers_eq_displacement_rank] at hw hq
  omega

theorem normalClosure_subquotient_offenderSubgroup
    (ρ : Representation (ZMod 2) G V) (a : G) (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 1)
    (W : Subrepresentation (ρ.comp (normalClosure ({a} : Set G)).subtype))
    (C : Subrepresentation W.toRepresentation) :
    offenderSubgroup C.quotientRepresentation = ⊤ := by
  let K := normalClosure ({a} : Set G)
  let J := offenderSubgroup C.quotientRepresentation
  have hKJ : K ≤ J.map K.subtype := by
    apply (Subgroup.closure_le (J.map K.subtype)).mpr
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    have hya : y = a := Set.mem_singleton_iff.mp hy
    subst y
    obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
    let t : K := ⟨g * a * g⁻¹, conjugatesOfSet_subset_normalClosure hx⟩
    have htp : t ^ 2 = 1 := by
      apply Subtype.ext
      change (g * a * g⁻¹) ^ 2 = 1
      rw [conj_pow, ha, mul_one, mul_inv_cancel]
    have htne : t ≠ 1 := by
      intro he
      apply hne
      have he' := congrArg (fun x : K => g⁻¹ * (x : G) * g) he
      simpa only [t, coe_mk, coe_one, mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, mul_one, one_mul] using he'
    have hr' : Module.finrank (ZMod 2)
        (LinearMap.range ((ρ.comp K.subtype) t - LinearMap.id)) ≤ 1 := by
      have he : (ρ.comp K.subtype) t = ρ (g * a * g⁻¹) := rfl
      rw [he]
      have hconj := fixedCodim_zpowers_conj ρ a g
      simp only [fixedCodim_zpowers_eq_displacement_rank] at hconj
      rw [hconj]
      exact hr
    have hb := bestOffender_of_involution_displacement_le_one C.quotientRepresentation t
      htp htne ((subquotient_displacement_rank_le (ρ.comp K.subtype) W C t).trans hr')
    have hJ : zpowers t ≤ J := le_iSup_of_le _ (le_iSup_of_le ⟨hb, le_top⟩ le_rfl)
    exact ⟨t, hJ (mem_zpowers t), rfl⟩
  apply top_unique
  intro k _
  obtain ⟨j, hj, he⟩ := hKJ k.property
  exact (show j = k from Subtype.ext he) ▸ hj
end Representation.BinaryOffender
