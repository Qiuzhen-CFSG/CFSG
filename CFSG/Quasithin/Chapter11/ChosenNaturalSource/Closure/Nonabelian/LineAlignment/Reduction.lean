module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.WeakClosure
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Calculus

/-!
# Normalization and the two intersection lines in 11.5.3(3)

Put W = Vᵍ and A = W ∩ T. The kernel B = C_A(V₂) has corank in W
at most one plus the rank of the actual action of A on V₂. The source
rank bound n, together with r ≥ (dimension − 1)n and n > 1, makes C_G(B)
normalize W. The commutator [V₂,A] then lies in V ∩ W. Applying 11.5.3(1)
also to g⁻¹ gives its two literal line bounds, one in each natural module.

The action-rank bound remains an explicit model input here. The subsequent
transvection/field-automorphism calculation is not asserted by these reductions.
Source: Aschbacher--Smith, 11.5.3(3), printed pp.779--780.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterE CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D} (F₀ : MarkedFlag E)

include F₀ in
/-- The actual original plane is normalized by the given Sylow subgroup. -/
theorem sylow_normalizes_plane : (T : Subgroup G) ≤ normalizer (E.V₂ : Set G) := by
  change _ ≤ normalizer (D.centralQuotientPreimage E.plane : Set G)
  rw [F₀.plane_eq]
  exact F₀.flag.invariant 1

include F₀ in
/-- The rank of the actual plane action bounds the kernel corank in Vᵍ. -/
theorem kernel_corank_le (g : G) {n : ℕ}
    (hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G)) ≤ 1)
    (haction : rank (inducedAutomizer E.V₂
      (V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G))) ≤ n) :
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      ((V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G)) ⊓
        centralizer (E.V₂ : Set G)) ≤ n + 1 := by
  let := D.elementary
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  rw [offender_corank_add inf_le_left inf_le_left,
    ← rank_inducedAutomizer E.V₂ _ (inf_le_right.trans (sylow_normalizes_plane F₀))]
  omega

/-- The source numerical inequalities force V₂ to normalize the original Vᵍ. -/
theorem plane_normalizes (g : G)
    (hr : (((F₀.action.dimension - 1) * E.input.field.degree : ℕ) : ℕ∞) ≤ globalR V)
    (hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G)) ≤ 1)
    (haction : rank (inducedAutomizer E.V₂
      (V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G))) ≤ E.input.field.degree) :
    E.V₂ ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hc := kernel_corank_le F₀ g hcor haction
  have hn : E.input.field.degree + 1 < (F₀.action.dimension - 1) * E.input.field.degree := by
    have h := E.input.nonbinary
    cases F₀.action <;> simp only [RemainingAction.dimension] <;> omega
  apply (le_centralizer_iff.mpr inf_le_right).trans
  apply centralizer_le_normalizer_of_corank_lt_globalR (inf_le_left.trans inf_le_left)
  rw [globalR_map_equiv]
  exact lt_of_lt_of_le (by exact_mod_cast lt_of_le_of_lt hc hn) hr

include F₀ in
/-- The fixed subgroup on Vᵍ also has corank at most n+1. -/
theorem fixed_corank_le (g : G)
    (hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G)) ≤ 1)
    (haction : rank (inducedAutomizer E.V₂
      (V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G))) ≤ E.input.field.degree) :
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (E.V₂ : Set G)) ≤
        E.input.field.degree + 1 := by
  apply le_trans _ (kernel_corank_le F₀ g hcor haction)
  apply Nat.log_mono_right
  exact relIndex_le_of_le_left (inf_le_inf_right _ inf_le_left)
    (by exact index_ne_zero_of_finite)

omit [Finite G] in
private theorem conjugate_cancel (P : Subgroup G) (g : G) :
    (P.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = P := by
  rw [map_map]
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv, MonoidHom.id_apply]
    group
  rw [he, map_id]

/-- Apply the same source intersection theorem in both natural modules.
The second line is literally the g-conjugate of an L-conjugate of V₁. -/
theorem intersection_two_lines
    (hintersection : ∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g).toMonoidHom ≤
        E.V₁.map (MulAut.conj l).toMonoidHom)
    (g : G) (hg : g ∉ normalizer (V : Set G)) :
    ∃ y ∈ L, ∃ l ∈ L, V ⊓ V.map (MulAut.conj g).toMonoidHom ≤
      E.V₁.map (MulAut.conj y).toMonoidHom ⊓
        (E.V₁.map (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨y, hy, hleft⟩ := hintersection g hg
  obtain ⟨l, hl, hright⟩ := hintersection g⁻¹ (fun h => hg (inv_mem_iff.mp h))
  refine ⟨y, hy, l, hl, le_inf hleft ?_⟩
  have h := map_mono (f := (MulAut.conj g).toMonoidHom) hright
  rw [map_inf _ _ _ (MulAut.conj g).injective, conjugate_cancel, inf_comm] at h
  exact h

include F₀ in
/-- Mutual normalization puts the actual moving subgroup into both modules. -/
theorem commutator_le_intersection (g : G)
    (hnorm : E.V₂ ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅E.V₂, V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G)⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom := by
  apply le_inf
  · exact (le_normalizer_iff_commutator_le_left.mp
      (inf_le_right.trans (sylow_normalizes_plane F₀))).trans
        (D.centralQuotientPreimage_le E.plane)
  · exact (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp hnorm)

include F₀ in
/-- The intersection theorem bounds the order of the literal commutator by q. -/
theorem commutator_card_le
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hintersection : ∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g).toMonoidHom ≤
        E.V₁.map (MulAut.conj l).toMonoidHom)
    (g : G) (hg : g ∉ normalizer (V : Set G))
    (hnorm : E.V₂ ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    Nat.card (⁅E.V₂, V.map (MulAut.conj g).toMonoidHom ⊓ (T : Subgroup G)⁆ : Subgroup G) ≤
      2 ^ E.input.field.degree := by
  obtain ⟨l, _, hl⟩ := hintersection g hg
  have h := Nat.card_le_card_of_injective
    (inclusion ((commutator_le_intersection F₀ g hnorm).trans hl))
    (inclusion_injective _)
  rwa [card_map_of_injective (MulAut.conj l).injective, card_line F₀ hfixed] at h

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.LineAlignment
