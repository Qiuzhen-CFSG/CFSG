module
public import Theory.Representation.BinaryNaturalDual.LowRankProfiles
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.CommonPure
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator
public import Theory.Representation.BinaryConjugationSection.DualHyperplanes
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryConjugationSection.CommutatorFixedExtension


/-!
# Low-rank profiles in the literal natural--dual quotient

The conjugation coordinates identify group commutators with the product of
the natural and contragredient moved spaces. Quadraticity makes this product
singular and supplies pure vectors; rank one gives two lines, and rank two
a plane and an orthogonal line. The quotient domain and kernel remain explicit.

Source: Aschbacher--Smith, 14.6.24(4), printed p.1041.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits
open scoped commutatorElement
namespace BinaryNaturalDual.LowRankProfiles
abbrev Vector := Fin 3 → ZMod 2
private instance : Finite (BinaryLinear.GL Vector) :=
  Finite.of_injective (fun g : BinaryLinear.GL Vector => (g : Vector → Vector))
    DFunLike.coe_injective
noncomputable abbrev natural : Representation (ZMod 2) (BinaryLinear.GL Vector) Vector :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom

theorem natural_injective : Function.Injective natural := by
  intro g h he
  exact LinearEquiv.ext (fun v => LinearMap.congr_fun he v)

theorem naturalDual_eq_prod : (naturalDualRepresentation :
    Representation (ZMod 2) (BinaryLinear.GL Vector) (Space Vector)) = natural.prod natural.dual := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  exact naturalDualRepresentation_apply g v

variable {G : Type*} [Group G] {H B Z : Subgroup G}
    (π : H →* BinaryLinear.GL Vector)
    (c : BinaryConjugationSection H B Z (naturalDualRepresentation.comp π))

/-- The literal commutator image splits along the two marked supports. -/
theorem section_commutator_product (A : Subgroup G) (hAH : A ≤ H) :
    c.imageSpace ⁅A,B⁆ =
      (subspaceCommutator natural ⊤ ((A.subgroupOf H).map π)).prod
        (subspaceCommutator natural.dual ⊤ ((A.subgroupOf H).map π)) := by
  have hB : c.imageSpace B = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨b,hb⟩ := c.onto (Multiplicative.ofAdd v)
    exact (c.mem_imageSpace_iff B v).mpr ⟨b,b.property,congrArg Multiplicative.toAdd hb⟩
  rw [c.imageSpace_commutator A B hAH le_rfl,hB,subspaceCommutator_comp_map,
    naturalDual_eq_prod,subspaceCommutator_prod]

include c in
theorem section_quadratic (A : Subgroup G) (hc : ⁅A,⁅A,B⁆⁆ ≤ Z) :
    IsQuadratic natural ((A.subgroupOf H).map π) := by
  have hq := BinaryConjugationSection.isQuadratic_of_triple_commutator_le
    H B Z A naturalDualRepresentation π c hc
  rw [naturalDual_eq_prod,quadratic_prod_iff] at hq
  exact hq.1

/-- Singularity and a nonzero pure vector are consequences of the action,
not additional orbit hypotheses. -/
theorem section_profile (A : Subgroup G) (hAH : A ≤ H)
    (hA : IsElementaryTwo ((A.subgroupOf H).map π)) (hc : ⁅A,⁅A,B⁆⁆ ≤ Z) :
    (∀ v ∈ c.imageSpace ⁅A,B⁆, quadratic v = 0) ∧
      ∃ v ∈ c.imageSpace ⁅A,B⁆, IsPure v := by
  apply orthogonal_product_profile c _ _ (section_commutator_product π c A hAH)
    (moved_orthogonal natural (section_quadratic π c A hc))
  left
  intro he
  have hp := fixedCodim_pos_of_faithful natural.dual (faithful_dual natural natural_injective) hA.1
  rw [fixedCodim_dual_eq_moved_finrank,he] at hp
  simp at hp

include c in
theorem section_rank_one (A : Subgroup G)
    (hA : IsElementaryTwo ((A.subgroupOf H).map π))
    (hr : rank ((A.subgroupOf H).map π) = 1) (hc : ⁅A,⁅A,B⁆⁆ ≤ Z) :
    Module.finrank (ZMod 2) (subspaceCommutator natural ⊤ ((A.subgroupOf H).map π)) = 1 ∧
    Module.finrank (ZMod 2) (subspaceCommutator natural.dual ⊤ ((A.subgroupOf H).map π)) = 1 :=
  rank_one_dimensions natural natural_injective (by simp [Vector]) _ hA hr
    (section_quadratic π c A hc)

include c in
theorem section_rank_two (A : Subgroup G)
    (hA : IsElementaryTwo ((A.subgroupOf H).map π))
    (hr : rank ((A.subgroupOf H).map π) = 2) (hc : ⁅A,⁅A,B⁆⁆ ≤ Z) :
    (Module.finrank (ZMod 2) (subspaceCommutator natural ⊤ ((A.subgroupOf H).map π)) = 1 ∧
      Module.finrank (ZMod 2) (subspaceCommutator natural.dual ⊤ ((A.subgroupOf H).map π)) = 2) ∨
    (Module.finrank (ZMod 2) (subspaceCommutator natural ⊤ ((A.subgroupOf H).map π)) = 2 ∧
      Module.finrank (ZMod 2) (subspaceCommutator natural.dual ⊤ ((A.subgroupOf H).map π)) = 1) :=
  rank_two_dimensions natural natural_injective (by simp [Vector]) _ hA hr
    (section_quadratic π c A hc)
/-- Retaining the fixed factor of U/Z gives the same singular profile for
the full original commutator subgroup [A,U]. -/
theorem section_profile_of_fixed_extension (A U C : Subgroup G)
    (hAH : A ≤ H) (hBU : B ≤ U)
    (hcover : ∀ u ∈ U, ∃ b ∈ B, ∃ t ∈ C, u = b * t)
    (hfixed : ⁅A,C⁆ ≤ Z)
    (hA : IsElementaryTwo ((A.subgroupOf H).map π)) (hc : ⁅A,⁅A,B⁆⁆ ≤ Z) :
    (∀ v ∈ c.imageSpace ⁅A,U⁆, quadratic v = 0) ∧
      ∃ v ∈ c.imageSpace ⁅A,U⁆, IsPure v := by
  rw [c.imageSpace_commutator_of_fixed_extension A U C hAH hBU hcover hfixed]
  exact section_profile π c A hAH hA hc

end BinaryNaturalDual.LowRankProfiles
