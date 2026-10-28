module
public import Theory.Representation.NormalElementaryQuotient
public import Mathlib.RepresentationTheory.Irreducible

/-!
# The faithful action on a minimal normal elementary subgroup

Subrepresentations of the actual centralizer-quotient action correspond to
ambient normal subgroups inside the elementary group. Minimal normality
therefore gives irreducibility, with the original quotient map unchanged.
-/

public section
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
open Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Minimal normality supplies irreducibility of the literal conjugation action. -/
theorem irreducible_of_minimal_normal (V : Subgroup G) [V.Normal]
    [IsElementaryAbelian 2 V] (hne : V ≠ ⊥)
    (hmin : ∀ D : Subgroup G, D.Normal → D ≤ V → D = ⊥ ∨ D = V)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G)) :
    IsIrreducible (representation V q hq hker) := by
  let ρ := representation V q hq hker
  let : Nontrivial V := (nontrivial_iff_ne_bot V).mpr hne
  rw [IsIrreducible,isSimpleOrder_iff]
  refine ⟨⟨⟨⊥,⊤,?_⟩⟩,?_⟩
  · intro hb
    have he : (⊥ : Submodule (ZMod 2) (Additive V)) = ⊤ :=
      congrArg Subrepresentation.toSubmodule hb
    exact bot_ne_top he
  intro P
  let D : Subgroup V := P.toSubmodule.toAddSubgroup.toSubgroup'
  let N := D.map V.subtype
  have hn : N.Normal := by
    constructor
    rintro _ ⟨v,hv,rfl⟩ g
    let w : V := ⟨g * (v : G) * g⁻¹,(inferInstance : V.Normal).conj_mem _ v.property g⟩
    refine ⟨w,?_,rfl⟩
    have hh := P.apply_mem_toSubmodule (q g) (show Additive.ofMul v ∈ P.toSubmodule from hv)
    have he : (ρ (q g) (Additive.ofMul v)).toMul = w := by
      apply Subtype.ext
      exact representation_apply V q hq hker g (Additive.ofMul v)
    change (ρ (q g) (Additive.ofMul v)).toMul ∈ D at hh
    rwa [he] at hh
  rcases hmin N hn (map_subtype_le _) with hb | he
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_antisymm _ bot_le
    intro v hv
    have hh : (v.toMul : G) ∈ N := mem_map_of_mem V.subtype hv
    rw [hb,mem_bot] at hh
    exact Additive.toMul.injective (Subtype.ext hh)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro v _
    have hh : (v.toMul : G) ∈ N := he.ge v.toMul.property
    obtain ⟨w,hw,heq⟩ := hh
    have heq' : w = v.toMul := Subtype.ext heq
    change v.toMul ∈ D
    rwa [heq'] at hw

end Representation.NormalElementaryQuotient
