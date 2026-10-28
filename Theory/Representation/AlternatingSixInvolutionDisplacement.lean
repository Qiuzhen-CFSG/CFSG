module

public import Theory.Representation.AlternatingFiveInvolutionDisplacement
public import Theory.SpecificGroups.Alternating.BlockEmbeddings
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.RestrictionComparison


/-!
# Binary involution displacement in A6

Restrict a faithful binary A6 representation to the standard embedded A5.
The proved A5 involution bound applies there; A6 involution fusion transports
it to every involution. Simplicity extends the conclusion to all nontrivial
A6 representations, and an actor containing an involution inherits the bound.

The final displacement-budget applications retain the literal invariant
submodule and quotient representations. Two nontrivial A6 sections cost at
least four dimensions. The S6 versions retain the actual even subgroup and
also allow actor subgroups containing odd permutations.

Source application: Meierfrankenfeld--Stellmacher (1993), Section 5.2(i),
printed p.914, in the binary natural S6 case. This is the chief-section
movement input; the critical-graph movement budget and chief-count assembly
are separate source arguments.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace Representation.AlternatingSixInvolutionDisplacement
private def fiveInvolution : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

private theorem fiveInvolution_order : orderOf fiveInvolution = 2 :=
  orderOf_eq_prime (by decide) (by decide)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every involution in a faithful binary A6 action moves at least two dimensions. -/
theorem displacement_lower (ρ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (hρ : Function.Injective ρ) (a : alternatingGroup (Fin 6)) (ha : orderOf a = 2) :
    2 ≤ Module.finrank (ZMod 2) (ρ a - LinearMap.id).range := by
  let f := alternatingGroup.degreeEmbedding (show 5 ≤ 6 by decide)
  have hf : Function.Injective f := alternatingGroup.degreeEmbedding_injective _
  have hlo := AlternatingFiveInvolutionDisplacement.displacement_lower (ρ.comp f)
    (hρ.comp hf) fiveInvolution fiveInvolution_order
  have ht : orderOf (f fiveInvolution) = 2 :=
    (orderOf_injective f hf fiveInvolution).trans fiveInvolution_order
  obtain ⟨c,hc⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj (f fiveInvolution) a ht ha)
  rw [← fixedCodim_zpowers_eq_displacement_rank,← hc,fixedCodim_zpowers_conj]
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact hlo

omit [FiniteDimensional (ZMod 2) V] in
private theorem injective_of_nontrivial
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (hρ : ∃ g, ρ g ≠ 1) : Function.Injective ρ := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (MonoidHom.normal_ker ρ).eq_bot_or_eq_top with hk | hk
  · exact ρ.ker_eq_bot_iff.mp hk
  · obtain ⟨g,hg⟩ := hρ
    exact (hg (show g ∈ ρ.ker from hk ▸ mem_top g)).elim

/-- Simplicity gives the same involution bound for every nontrivial binary A6 action. -/
theorem displacement_lower_of_nontrivial
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (hρ : ∃ g, ρ g ≠ 1) (a : alternatingGroup (Fin 6)) (ha : orderOf a = 2) :
    2 ≤ Module.finrank (ZMod 2) (ρ a - LinearMap.id).range :=
  displacement_lower ρ (injective_of_nontrivial ρ hρ) a ha

/-- One involution of displacement at most one forces the entire A6 action to be trivial. -/
theorem trivial_of_displacement_le_one
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (a : alternatingGroup (Fin 6)) (ha : orderOf a = 2)
    (hr : Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≤ 1) :
    ∀ g, ρ g = 1 := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (MonoidHom.normal_ker ρ).eq_bot_or_eq_top with hk | hk
  · have h := displacement_lower ρ (ρ.ker_eq_bot_iff.mp hk) a ha
    omega
  · intro g
    exact show g ∈ ρ.ker from hk ▸ mem_top g

/-- Any actor subgroup containing an involution costs at least two dimensions
in a nontrivial binary A6 action. -/
theorem fixedCodim_lower_of_involution_mem
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (hρ : ∃ g, ρ g ≠ 1) {A : Subgroup (alternatingGroup (Fin 6))}
    (a : alternatingGroup (Fin 6)) (ha : orderOf a = 2) (haA : a ∈ A) :
    2 ≤ fixedCodim ρ A := by
  have hl := displacement_lower_of_nontrivial ρ hρ a ha
  rw [← fixedCodim_zpowers_eq_displacement_rank] at hl
  have hdim := Submodule.finrank_mono
    (fixedSpace_antitone ρ (zpowers_le.mpr haA))
  have hA := fixedCodim_add_finrank ρ A
  have ha' := fixedCodim_add_finrank ρ (zpowers a)
  omega

/-- A subgroup of fixed codimension at most one containing an involution
forces the entire A6 action to be trivial. -/
theorem trivial_of_fixedCodim_le_one
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    {A : Subgroup (alternatingGroup (Fin 6))}
    (a : alternatingGroup (Fin 6)) (ha : orderOf a = 2) (haA : a ∈ A)
    (hA : fixedCodim ρ A ≤ 1) : ∀ g, ρ g = 1 := by
  classical
  by_contra h
  push Not at h
  have hl := fixedCodim_lower_of_involution_mem ρ h a ha haA
  omega

/-- The literal submodule and quotient actions, when both nontrivial, cost
at least four dimensions for every actor subgroup containing an involution. -/
theorem four_le_fixedCodim_of_nontrivial_submodule_and_quotient
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (U : Subrepresentation ρ)
    (hU : ∃ g, U.toRepresentation g ≠ 1)
    (hQ : ∃ g, U.quotientRepresentation g ≠ 1)
    {A : Subgroup (alternatingGroup (Fin 6))}
    (a : alternatingGroup (Fin 6)) (ha : orderOf a = 2) (haA : a ∈ A) :
    4 ≤ fixedCodim ρ A := by
  have hU' := fixedCodim_lower_of_involution_mem U.toRepresentation hU a ha haA
  have hQ' := fixedCodim_lower_of_involution_mem U.quotientRepresentation hQ a ha haA
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ U A
  omega

/-- The source 5.2(i) displacement-budget consumer on the literal quotient:
with movement at most three, the lower space or its quotient is centralized. -/
theorem submodule_or_quotient_trivial_of_fixedCodim_le_three
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (U : Subrepresentation ρ) {A : Subgroup (alternatingGroup (Fin 6))}
    (a : alternatingGroup (Fin 6)) (ha : orderOf a = 2) (haA : a ∈ A)
    (hA : fixedCodim ρ A ≤ 3) :
    (∀ g, U.toRepresentation g = 1) ∨ (∀ g, U.quotientRepresentation g = 1) := by
  classical
  by_contra h
  push Not at h
  have hl := four_le_fixedCodim_of_nontrivial_submodule_and_quotient ρ U h.1 h.2 a ha haA
  omega

/-- An actual S6 actor containing an even involution has fixed codimension at
least two whenever its restriction to the literal A6 subgroup is nontrivial. -/
theorem fixedCodim_lower_of_even_involution_mem
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (hρ : ∃ g : alternatingGroup (Fin 6), ρ g ≠ 1)
    {A : Subgroup (Equiv.Perm (Fin 6))} (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A) :
    2 ≤ fixedCodim ρ A := by
  let b : alternatingGroup (Fin 6) := ⟨a,heven⟩
  have hb : orderOf b = 2 :=
    (orderOf_injective (alternatingGroup (Fin 6)).subtype Subtype.coe_injective b).symm.trans ha
  have hl := displacement_lower_of_nontrivial
    (ρ.comp (alternatingGroup (Fin 6)).subtype) hρ b hb
  change 2 ≤ Module.finrank (ZMod 2) (ρ a - LinearMap.id).range at hl
  rw [← fixedCodim_zpowers_eq_displacement_rank] at hl
  have hdim := Submodule.finrank_mono
    (fixedSpace_antitone ρ (zpowers_le.mpr haA))
  have hA := fixedCodim_add_finrank ρ A
  have ha' := fixedCodim_add_finrank ρ (zpowers a)
  omega

/-- The literal S6 submodule and quotient cost four dimensions when both
restrictions to A6 are nontrivial and the actor contains an even involution. -/
theorem four_le_fixedCodim_of_nontrivial_even_sections
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (U : Subrepresentation ρ)
    (hU : ∃ g : alternatingGroup (Fin 6), U.toRepresentation g ≠ 1)
    (hQ : ∃ g : alternatingGroup (Fin 6), U.quotientRepresentation g ≠ 1)
    {A : Subgroup (Equiv.Perm (Fin 6))} (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A) :
    4 ≤ fixedCodim ρ A := by
  have hU' := fixedCodim_lower_of_even_involution_mem U.toRepresentation hU a ha heven haA
  have hQ' := fixedCodim_lower_of_even_involution_mem U.quotientRepresentation hQ a ha heven haA
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ U A
  omega

/-- The source 5.2(i) budget on an actual S6 section: with movement at most
three, A6 centralizes the lower section or the literal upper quotient. -/
theorem even_submodule_or_quotient_trivial_of_fixedCodim_le_three
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (U : Subrepresentation ρ) {A : Subgroup (Equiv.Perm (Fin 6))}
    (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6)) (haA : a ∈ A)
    (hA : fixedCodim ρ A ≤ 3) :
    (∀ g : alternatingGroup (Fin 6), U.toRepresentation g = 1) ∨
      (∀ g : alternatingGroup (Fin 6), U.quotientRepresentation g = 1) := by
  classical
  by_contra h
  push Not at h
  have hl := four_le_fixedCodim_of_nontrivial_even_sections ρ U h.1 h.2 a ha heven haA
  omega

end Representation.AlternatingSixInvolutionDisplacement
