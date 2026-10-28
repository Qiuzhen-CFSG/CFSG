module

public import Theory.GroupTheory.SimpleSectionNormalAlternative
public import Mathlib.GroupTheory.Solvable

/-!
# Simple sections after removing two solvable layers

Suppose N is normal in G with solvable quotient, R is a solvable normal
subgroup of N, and N/R embeds into H. Every nonsolvable simple section
of G is then a section of H. Apply the normal-subgroup section alternative
twice, and transport the remaining subgroup along the faithful map.

This is the elementary extension argument for composition factors. Normality
of R is required only inside N, and the map is from the actual quotient N/R.
Neither finiteness nor a classification theorem is needed.
-/

namespace Theory.GroupTheory

/-- A solvable normal layer and a solvable outer layer leave a group
faithfully represented inside `H`. -/
@[expose] public def SolvableLayersEmbedding
    (G H : Type*) [Group G] [Group H] : Prop :=
  ∃ (N : Subgroup G) (hN : N.Normal),
    letI := hN
    Group.IsSolvable (G ⧸ N) ∧
      ∃ (R : Subgroup N) (hR : R.Normal),
        letI := hR
        Group.IsSolvable R ∧
          ∃ j : (N ⧸ R) →* H, Function.Injective j

/-- A simple section either comes from a solvable layer or is an actual
simple image of a subgroup of the target of the faithful representation. -/
public theorem SolvableLayersEmbedding.simpleSection
    {G H S : Type*} [Group G] [Group H] [Group S] [IsSimpleGroup S]
    (h : SolvableLayersEmbedding G H)
    (U : Subgroup G) (f : U →* S) (hf : Function.Surjective f) :
    Group.IsSolvable S ∨ ∃ W : Subgroup H, ∃ g : W →* S,
      Function.Surjective g := by
  obtain ⟨N, hN, hQ, R, hR, hsolv, j, hj⟩ := h
  let := hN
  let := hR
  rcases Subgroup.simple_section_normal_or_quotient N U f hf with
    ⟨V, g, hg⟩ | ⟨V, g, hg⟩
  · rcases Subgroup.simple_section_normal_or_quotient R V g hg with
      ⟨W, k, hk⟩ | ⟨W, k, hk⟩
    · let := hsolv
      exact Or.inl (Group.isSolvable_of_surjective hk)
    · let e := Subgroup.equivMapOfInjective W j hj
      exact Or.inr ⟨W.map j, k.comp e.symm.toMonoidHom,
        hk.comp e.symm.surjective⟩
  · let := hQ
    exact Or.inl (Group.isSolvable_of_surjective hg)

end Theory.GroupTheory
