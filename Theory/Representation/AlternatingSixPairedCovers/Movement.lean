module
public import Theory.Representation.AlternatingSixPairedCovers.Inputs
public import Theory.Representation.AlternatingSixPairedCovers.MovementCubic
public import Theory.Representation.BinaryPermutationSixCover.Movement
public import Theory.Representation.BinaryOffender.CubicFixedQuotient
public import Theory.Representation.AlternatingSixInvolutionDisplacement
public import Theory.Representation.SixLetterTransvections

/-!
# Nontrivial sections and movement on paired A₆ covers

The same marked three-cycle moves at most two dimensions on the first cover
and at least four on its companion. Cubic averaging therefore proves that
the quotient by the first cover is nontrivial. Simplicity makes both actual
sections faithful, giving movement at least four for every nonidentity
component element. An actor moving at most one dimension has commutators
of movement at most two, so it centralizes the component and is the identity.
This last argument allows the actor to interchange the two covers.

These results discharge hU, hQ and hno in the original-source consumer
AlternatingSix.Application. The stronger outer-involution bound three and
the simultaneous quadratic-actor classification remain separate obligations
of qt-e-suitable-component-marking; suitable-choice assembly belongs to
qt-e-suitable-existence. Source: Aschbacher–Smith 14.6.24(2), p.1041.
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace AlternatingSixPairedCovers.Data
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]
variable {ρ : Representation (ZMod 2) H E} (C : Data ρ)

omit [FiniteDimensional (ZMod 2) E] in
/-- The marked three-cycle acts nontrivially on the first covering support. -/
theorem first_threeCycle_ne_one :
    C.first.toRepresentation GLS3.Chapter5.baseThreeCycle ≠ 1 := by
  have hi := C.first_model.injective (alternatingGroup (Fin 6)).subtype_injective
  intro h
  have he : GLS3.Chapter5.baseThreeCycle = 1 := hi (h.trans (map_one _).symm)
  have hn : GLS3.Chapter5.baseThreeCycle ≠ 1 := by decide +kernel
  exact hn he

omit [FiniteDimensional (ZMod 2) E] in
/-- The same marked three-cycle moves at most two dimensions on the first
cover but at least four on the companion. -/
theorem threeCycle_separates_supports :
    fixedCodim C.first.toRepresentation (zpowers GLS3.Chapter5.baseThreeCycle) ≤ 2 ∧
    4 ≤ fixedCodim C.second.toRepresentation (zpowers GLS3.Chapter5.baseThreeCycle) := by
  have h₁ := (C.first_model.fixedCodim_bounds (zpowers GLS3.Chapter5.baseThreeCycle)).2
  have h₂ := (C.second_model.fixedCodim_bounds (zpowers GLS3.Chapter5.baseThreeCycle)).1
  rw [MonoidHom.map_zpowers] at h₁ h₂
  change fixedCodim C.first.toRepresentation _ ≤ fixedCodim
    (BinaryPermutation.coreRepresentation (Fin 6)) (zpowers GLS3.Chapter5.threeCyclePerm) at h₁
  rw [core_threeCycle_fixedCodim] at h₁
  change fixedCodim (BinaryPermutation.naturalRepresentation (Fin 6))
    (zpowers (BinaryAlternatingSix.diagramAut GLS3.Chapter5.threeCyclePerm)) ≤ _ at h₂
  rw [natural_diagram_threeCycle_fixedCodim] at h₂
  exact ⟨h₁,h₂⟩

/-- The companion cannot disappear in the literal quotient by the first
cover, even when the supports share central vectors. -/
theorem quotient_threeCycle_ne_one :
    C.first.quotientRepresentation GLS3.Chapter5.baseThreeCycle ≠ 1 := by
  intro hq
  have he := fixedCodim_cubic_eq_subrepresentation (ρ.comp C.component) C.first
    GLS3.Chapter5.baseThreeCycle (by decide +kernel) hq
  have hs := fixedCodim_subrepresentation_le (ρ.comp C.component) C.second
    (zpowers GLS3.Chapter5.baseThreeCycle)
  have hb := C.threeCycle_separates_supports
  omega

/-- Both actual sections needed by the terminal A6 obstruction are nontrivial. -/
theorem nontrivial_sections :
    (∃ g, C.first.toRepresentation g ≠ 1) ∧
      (∃ g, C.first.quotientRepresentation g ≠ 1) :=
  ⟨⟨GLS3.Chapter5.baseThreeCycle,C.first_threeCycle_ne_one⟩,
    ⟨GLS3.Chapter5.baseThreeCycle,C.quotient_threeCycle_ne_one⟩⟩

/-- Every involution of the same embedded component moves at least four
ambient dimensions. -/
theorem component_involution_movement (t : alternatingGroup (Fin 6))
    (ht : orderOf t = 2) : 4 ≤ fixedCodim ρ (zpowers (C.component t)) := by
  have hh := Representation.AlternatingSixInvolutionDisplacement.four_le_fixedCodim_of_nontrivial_submodule_and_quotient
    (ρ.comp C.component) C.first C.nontrivial_sections.1 C.nontrivial_sections.2
    t ht (mem_zpowers t)
  change 4 ≤ Module.finrank (ZMod 2) (E ⧸ fixedSpace (ρ.comp C.component) (zpowers t)) at hh
  rw [fixedSpace_comp_map,MonoidHom.map_zpowers] at hh
  exact hh

private theorem alternating_injective_of_nontrivial
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (hs : ∃ g, σ g ≠ 1) : Function.Injective σ := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (MonoidHom.normal_ker σ).eq_bot_or_eq_top with hk | hk
  · exact σ.ker_eq_bot_iff.mp hk
  · obtain ⟨g,hg⟩ := hs
    exact (hg (show g ∈ σ.ker from hk ▸ mem_top g)).elim

private theorem alternating_two_le_movement {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
      [FiniteDimensional (ZMod 2) V]
      (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
      (hs : ∃ g, σ g ≠ 1) (t : alternatingGroup (Fin 6)) (ht : t ≠ 1) : 2 ≤ fixedCodim σ (zpowers t) := by
    by_contra hn
    have he := Representation.SixLetterTransvections.alternating_eq_one_of_displacement_le_one
      σ (alternating_injective_of_nontrivial σ hs) t
      (by rw [←fixedCodim_zpowers_eq_displacement_rank]; omega)
    exact ht he

/-- The two faithful component sections cost at least four dimensions for
any nonidentity element, not just involutions. -/
theorem component_movement (t : alternatingGroup (Fin 6)) (ht : t ≠ 1) :
    4 ≤ fixedCodim ρ (zpowers (C.component t)) := by
  have h₁ := alternating_two_le_movement C.first.toRepresentation C.nontrivial_sections.1 t ht
  have h₂ := alternating_two_le_movement C.first.quotientRepresentation C.nontrivial_sections.2 t ht
  have hh := fixedCodim_quotient_add_subrepresentation_le (ρ.comp C.component)
    C.first (zpowers t)
  have hl : 4 ≤ fixedCodim (ρ.comp C.component) (zpowers t) := by omega
  change 4 ≤ Module.finrank (ZMod 2) (E ⧸ fixedSpace (ρ.comp C.component) (zpowers t)) at hl
  rw [fixedSpace_comp_map,MonoidHom.map_zpowers] at hl
  exact hl

include C in
/-- A small-displacement actor centralizes the component: each commutator
has displacement at most two, whereas nonidentity component elements move
at least four. Self-centralization therefore excludes every transvection,
including actors interchanging the covering supports. -/
theorem two_le_movement (a : H) (ha : a ≠ 1) : 2 ≤ fixedCodim ρ (zpowers a) := by
  by_contra hn
  have ha1 : fixedCodim ρ (zpowers a) ≤ 1 := by omega
  have hc : a ∈ Subgroup.centralizer (C.component.range : Set H) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨t,rfl⟩
    have hm : a * C.component t * a⁻¹ * (C.component t)⁻¹ ∈ C.component.range :=
      (C.component.range).mul_mem (C.normal.conj_mem _ ⟨t,rfl⟩ a)
        ((C.component.range).inv_mem ⟨t,rfl⟩)
    obtain ⟨s,hs⟩ := hm
    have hr := fixedCodim_commutator_le_twice ρ a (C.component t)
    have he : a * C.component t * a⁻¹ * (C.component t)⁻¹ = 1 := by
      by_cases hz : s = 1
      · simpa only [hz,map_one] using hs.symm
      · have hl := C.component_movement s hz
        rw [hs] at hl
        omega
    have he' := congrArg (fun x : H => x * (C.component t * a)) he
    have hh : a * C.component t = C.component t * a := by
      simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one,one_mul] using he'
    exact hh.symm
  rw [C.centralizer] at hc
  exact ha hc

end AlternatingSixPairedCovers.Data
