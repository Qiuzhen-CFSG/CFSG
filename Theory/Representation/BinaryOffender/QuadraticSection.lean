module

public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.Ratio

/-!
# Quadratic actions on sections and direct sums

Quadratic action passes to a literal invariant section. Fixed codimension is
additive on direct sums, so doubling a module doubles the cost of an actor
without doubling the actor's rank. We also extract an actual quadratic actor
from a global ratio bound of two, and lift the absence of transvections from
a faithful section.

These are the linear steps used for the paired chief factors in
Aschbacher–Smith 13.8.21(1), printed pp.956–957 (1 March 2004 manuscript).
They do not classify chief factors or identify a parabolic subgroup.
-/

public section
open Representation
open scoped ENNReal
namespace Representation.BinaryOffender
variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)

/-- Quadratic action restricts to an invariant subspace. -/
theorem quadratic_subrepresentation (N : Subrepresentation ρ)
    {A : Subgroup G} (hq : IsQuadratic ρ A) : IsQuadratic N.toRepresentation A := by
  intro a ha b hb v
  exact Subtype.ext (hq a ha b hb v)

/-- Quadratic action descends to the actual section `N / (L ∩ N)`. -/
theorem quadratic_section (L N : Subrepresentation ρ)
    {A : Subgroup G} (hq : IsQuadratic ρ A) :
    IsQuadratic (sectionRepresentation ρ L N) A := by
  exact quadratic_of_equivariant_surjection N.toRepresentation
    (sectionRepresentation ρ L N) (sectionLower ρ L N).toSubmodule.mkQ
    (sectionLower ρ L N).toSubmodule.mkQ_surjective
    (fun _ _ => rfl) A (quadratic_subrepresentation ρ N hq)

/-- Both summands must be quadratic under the same actor. -/
theorem quadratic_prod_iff (A : Subgroup G) :
    IsQuadratic (ρ.prod σ) A ↔ IsQuadratic ρ A ∧ IsQuadratic σ A := by
  constructor
  · intro h
    exact ⟨fun a ha b hb v => congrArg Prod.fst (h a ha b hb (v, 0)),
      fun a ha b hb w => congrArg Prod.snd (h a ha b hb (0, w))⟩
  · rintro ⟨hρ, hσ⟩ a ha b hb v
    exact Prod.ext (hρ a ha b hb v.1) (hσ a ha b hb v.2)

/-- A pair is fixed precisely when each coordinate is fixed. -/
theorem fixedSpace_prod (A : Subgroup G) :
    fixedSpace (ρ.prod σ) A = (fixedSpace ρ A).prod (fixedSpace σ A) := by
  ext v
  constructor
  · intro h
    exact ⟨fun a => congrArg Prod.fst (h a), fun a => congrArg Prod.snd (h a)⟩
  · rintro ⟨hρ, hσ⟩ a
    exact Prod.ext (hρ a) (hσ a)

/-- Codimensions add, while the acting subgroup remains the same. -/
theorem fixedCodim_prod [FiniteDimensional (ZMod 2) V]
    [FiniteDimensional (ZMod 2) W] (A : Subgroup G) :
    fixedCodim (ρ.prod σ) A = fixedCodim ρ A + fixedCodim σ A := by
  have hp := fixedCodim_add_finrank (ρ.prod σ) A
  have hρ := fixedCodim_add_finrank ρ A
  have hσ := fixedCodim_add_finrank σ A
  rw [fixedSpace_prod] at hp
  let e : (fixedSpace ρ A).prod (fixedSpace σ A) ≃ₗ[ZMod 2]
      (fixedSpace ρ A) × (fixedSpace σ A) :=
    { toFun := fun v => (⟨v.val.1, v.property.1⟩, ⟨v.val.2, v.property.2⟩)
      invFun := fun v => ⟨(v.1.val, v.2.val), v.1.property, v.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have he := e.finrank_eq
  rw [Module.finrank_prod] at he hp
  omega

/-- The finite infimum in `q ≤ 2` supplies a nontrivial quadratic actor. -/
theorem quadraticRatio_le_two_iff [Finite G] :
    quadraticRatio ρ ≤ 2 ↔
      ∃ A, IsElementaryTwo A ∧ IsQuadratic ρ A ∧ fixedCodim ρ A ≤ 2 * rank A := by
  rw [quadraticRatio_le_iff ρ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
  have hratio {A : Subgroup G} (hA : IsElementaryTwo A) :
      actionRatio ρ A ≤ 2 ↔ fixedCodim ρ A ≤ 2 * rank A := by
    have h0 : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA.rank_pos)
    rw [actionRatio, ENNReal.div_le_iff h0 (by simp)]
    exact_mod_cast Iff.rfl
  constructor
  · rintro ⟨A, hA, hq, hr⟩
    exact ⟨A, hA, hq, (hratio hA).mp hr⟩
  · rintro ⟨A, hA, hq, hr⟩
    exact ⟨A, hA, hq, (hratio hA).mpr hr⟩

/-- Faithfulness is necessary: a transvection could act trivially on an
unfaithful section. -/
theorem no_transvection_of_faithful_section [FiniteDimensional (ZMod 2) V]
    (L N : Subrepresentation ρ)
    (hfaith : Function.Injective (sectionRepresentation ρ L N))
    (hsection : ∀ g : G, fixedCodim (sectionRepresentation ρ L N) (Subgroup.zpowers g) ≠ 1) :
    ∀ g : G, fixedCodim ρ (Subgroup.zpowers g) ≠ 1 := by
  intro g hg
  have hle := fixedCodim_section_le ρ L N (Subgroup.zpowers g)
  have hz : fixedCodim (sectionRepresentation ρ L N) (Subgroup.zpowers g) = 0 := by
    have := hsection g
    omega
  have hfix := (fixedCodim_eq_zero_iff _ _).mp hz
  have he : sectionRepresentation ρ L N g = sectionRepresentation ρ L N 1 := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ fixedSpace (sectionRepresentation ρ L N) (Subgroup.zpowers g) := by
      rw [hfix]
      trivial
    simpa using hv ⟨g, Subgroup.mem_zpowers g⟩
  have hg1 := hfaith he
  subst g
  have hbot : Subgroup.zpowers (1 : G) = ⊥ := by simp
  rw [hbot] at hg
  have hz := (fixedCodim_eq_zero_iff ρ ⊥).mpr (fixedSpace_bot ρ)
  omega
end Representation.BinaryOffender
