module

public import Theory.GroupTheory.SimpleSectionSolvableReduction.Model
public import Mathlib.GroupTheory.Sylow

/-!
# Two-subgroup exponents in simple sections

The property that every two-subgroup has exponent two passes to sections:
lift a Sylow subgroup through the section epimorphism, then use the original
subgroup inclusion. A solvable kernel can first be removed when the section
is nonsolvable and simple. This keeps the actual representation map, without
assuming that an arbitrary quotient preserves elementary abelian ranks.

Source application: the rank-one Levi quotients in Aschbacher--Smith 4.4.12,
printed pp.621--622.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.SimpleSection

variable {X S A : Type*} [Group X] [Finite X] [Group S] [Group A]

/-- The two-subgroup exponent bound passes to every actual section. -/
theorem two_exponent_of_section
    (hX : ∀ P : Subgroup X, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (U : Subgroup X) (f : U →* S) (hf : Function.Surjective f) :
    ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  intro P hp x
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  obtain ⟨R,hR⟩ := Sylow.mapSurjective_surjective hf 2 Q
  have hx : (x : S) ∈ (R : Subgroup U).map f := by
    change (x : S) ∈ (R.mapSurjective hf : Subgroup S)
    rw [hR]
    exact hQ x.property
  obtain ⟨a,ha,he⟩ := hx
  have hs : (a : X) ^ 2 = 1 := congrArg Subtype.val
    (hX ((R : Subgroup U).map U.subtype) (R.isPGroup'.map U.subtype)
      ⟨a,mem_map_of_mem U.subtype ha⟩)
  have hs' : a ^ 2 = 1 := Subtype.ext hs
  apply Subtype.ext
  simpa only [map_pow,map_one,he,Subgroup.coe_pow,Subgroup.coe_one] using congrArg f hs'

/-- A solvable-kernel representation transfers the exponent bound to every
nonsolvable simple quotient of its domain. -/
theorem two_exponent_of_solvable_representation [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S)
    (hX : ∀ P : Subgroup X, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (f : A →* X) [Group.IsSolvable f.ker]
    (π : A →* S) (hπ : Function.Surjective π) :
    ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  let m : Group.SolvableKernelModel A f.range := {
    kernel := f.ker
    normal := inferInstance
    solvable := inferInstance
    quotientEquiv := QuotientGroup.quotientKerEquivRange f }
  obtain ⟨U,g,hg⟩ := m.simple_section hS ⊤
    (π.comp (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom)
    (hπ.comp topEquiv.surjective)
  apply two_exponent_of_section (X := f.range) ?_ U g hg
  intro P hp x
  have he := hX (P.map f.range.subtype) (hp.map f.range.subtype)
    ⟨x,mem_map_of_mem f.range.subtype x.property⟩
  apply Subtype.ext
  apply Subtype.ext
  simpa only [Subgroup.coe_pow,Subgroup.coe_one] using congrArg Subtype.val he

end Theory.GroupTheory.SimpleSection
