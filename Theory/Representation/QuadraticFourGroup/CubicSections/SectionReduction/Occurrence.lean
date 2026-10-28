module

public import Theory.Representation.QuadraticFourGroup.CubicSections.SectionReduction.Transport
public import Theory.Representation.SimpleHeadQuotient
public import Mathlib.Order.Atoms.Finite

/-!
# Occurrence of restricted sections in ambient composition factors

A prescribed irreducible section of a restricted finite-dimensional binary
representation occurs in the restriction of an actual ambient irreducible
subquotient. Choose a minimal ambient invariant subspace containing the
prescribed section, then a maximal proper invariant subspace of it. Intersect
the subspace presenting the section with this maximal subspace. Its image in
the prescribed irreducible section is either zero or surjective. Surjectivity contradicts minimality; the zero case factors the
section map through the ambient quotient.

This is the section-occurrence reduction used in GLS, volume 2,
Theorem 25.14, Step 2 (Chapter G, lines 824–849). All subspaces, quotient
actions and equivariant equivalences are literal. The argument works for any
homomorphism of acting groups, without normality or injectivity.
-/

public section

open Representation
namespace Representation.QuadraticFourGroup
variable {k G V W Z : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup Z] [Module k Z]
  {ρ : Representation k G V} {σ : Representation k G W} {τ : Representation k G Z}

/-- Realize a section by an equivariant epimorphism from an invariant subspace. -/
private theorem section_iff_surjection : IsIrreducibleSection ρ σ ↔
    σ.IsIrreducible ∧ ∃ S : Subrepresentation ρ,
      ∃ f : S.toRepresentation.IntertwiningMap σ, Function.Surjective f := by
  constructor
  · rintro ⟨hi, S, N, ⟨e⟩⟩
    let q : S.toRepresentation.IntertwiningMap N.quotientRepresentation := {
      toLinearMap := N.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
    exact ⟨hi, S, e.toIntertwiningMap.comp q,
      e.toLinearEquiv.surjective.comp N.toSubmodule.mkQ_surjective⟩
  · rintro ⟨hi, S, f, hf⟩
    refine ⟨hi, S, f.ker, ⟨.mk (f.toLinearMap.quotKerEquivOfSurjective hf) ?_⟩⟩
    intro g
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with
    | H v => exact LinearMap.congr_fun (f.isIntertwining' g) v

set_option backward.isDefEq.respectTransparency false in
/-- Exactness for equivariant linear maps, retaining the specified target action. -/
private theorem factor_surjection
    (q : ρ.IntertwiningMap τ) (hq : Function.Surjective q)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (hk : q.ker ≤ f.ker) :
    ∃ p : τ.IntertwiningMap σ, Function.Surjective p := by
  let e := q.toLinearMap.quotKerEquivOfSurjective hq
  let l := q.ker.toSubmodule.liftQ f.toLinearMap hk
  let p := l.comp e.symm.toLinearMap
  have hp (v : V) : p (q v) = f v := by
    change l (e.symm (q v)) = f v
    have he : e.symm (q v) = Submodule.Quotient.mk v :=
      LinearMap.quotKerEquivOfSurjective_symm_apply (f := q.toLinearMap) hq v
    rw [he]
    rfl
  let p' : τ.IntertwiningMap σ := {
    toLinearMap := p
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro z
      obtain ⟨v, rfl⟩ := hq z
      change p (τ g (q v)) = σ g (p (q v))
      rw [← q.isIntertwining, hp, f.isIntertwining, hp] }
  refine ⟨p', ?_⟩
  intro w
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨q v, hp v⟩

namespace SectionReduction
variable {X E : Type*} [Group X] [Group E]

set_option backward.isDefEq.respectTransparency false in
/-- Every prescribed irreducible section of a restriction occurs in the
restriction of an ambient irreducible invariant subquotient. -/
theorem exists_irreducible_section_occurrence
    {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) X V) (i : E →* X)
    (σ : Representation (ZMod 2) E W) (hs : IsIrreducibleSection (ρ.comp i) σ) :
    ∃ U : Subrepresentation ρ, ∃ N : Subrepresentation U.toRepresentation,
      N.quotientRepresentation.IsIrreducible ∧
        IsIrreducibleSection (N.quotientRepresentation.comp i) σ := by
  classical
  let := hs.1
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Subrepresentation ρ) :=
    Finite.of_injective (fun U : Subrepresentation ρ => (U : Set V)) SetLike.coe_injective
  -- Minimize the ambient subspace while retaining a map onto the given section.
  let P : Subrepresentation ρ → Prop := fun U =>
    ∃ S : Subrepresentation (ρ.comp i), S.toSubmodule ≤ U.toSubmodule ∧
      ∃ f : S.toRepresentation.IntertwiningMap σ, Function.Surjective f
  have hP : ∃ U, P U := by
    obtain ⟨_, S, f, hf⟩ := section_iff_surjection.mp hs
    exact ⟨⊤, S, le_top, f, hf⟩
  obtain ⟨U, hU, hmin⟩ := (inferInstance : WellFoundedLT (Subrepresentation ρ)).exists_minimal
    {U | P U} hP
  obtain ⟨S, hSU, f, hf⟩ := hU
  have hUne : U.toSubmodule ≠ ⊥ := by
    intro he
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨v, rfl⟩ := hf w
    have hv : (v : V) = 0 := by
      have hm := hSU v.property
      rwa [he, Submodule.mem_bot] at hm
    have hv' : v = 0 := Subtype.ext hv
    exact hw (hv' ▸ map_zero f)
  let : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hUne
  let : IsCoatomic (Subrepresentation U.toRepresentation) :=
    SimpleHeadQuotient.subrepresentation_coatomic U.toRepresentation
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (Subrepresentation U.toRepresentation)
  refine ⟨U, N, SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN, ?_⟩
  let T : Subrepresentation ρ := {
    toSubmodule := N.toSubmodule.map U.toSubmodule.subtype
    apply_mem_toSubmodule g v hv := by
      obtain ⟨u, hu, rfl⟩ := hv
      exact ⟨U.toRepresentation g u, N.apply_mem_toSubmodule g hu, rfl⟩ }
  have hTU : T ≤ U := Submodule.map_subtype_le _ _
  have hTne : T ≠ U := by
    intro he
    apply hN.1
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro u _
    obtain ⟨v, hv, hvu⟩ := (show (u : V) ∈ T from he.symm ▸ u.property)
    exact (Subtype.ext hvu : v = u) ▸ hv
  let K : Subrepresentation (ρ.comp i) := {
    toSubmodule := S.toSubmodule ⊓ T.toSubmodule
    apply_mem_toSubmodule g v hv :=
      ⟨S.apply_mem_toSubmodule g hv.1, T.apply_mem_toSubmodule (i g) hv.2⟩ }
  let j : K.toRepresentation.IntertwiningMap S.toRepresentation := {
    toLinearMap := Submodule.inclusion (show K.toSubmodule ≤ S.toSubmodule from inf_le_left)
    isIntertwining' := fun _ => rfl }
  -- The intersection with the maximal subspace cannot still surject onto σ.
  have hz : f.comp j = 0 := by
    rcases IsIrreducible.surjective_or_eq_zero (f.comp j) with hsurj | hz
    · exact False.elim (hTne (le_antisymm hTU
        (hmin (show P T from ⟨K, inf_le_right, f.comp j, hsurj⟩) hTU)))
    · exact hz
  -- Thus the prescribed section map descends to the image in U / N.
  let a : S.toRepresentation.IntertwiningMap (U.toRepresentation.comp i) := {
    toLinearMap := Submodule.inclusion hSU
    isIntertwining' := fun _ => rfl }
  let q : Representation.IntertwiningMap (U.toRepresentation.comp i)
      (N.quotientRepresentation.comp i) := {
    toLinearMap := N.toSubmodule.mkQ
    isIntertwining' := fun _ => rfl }
  let b := q.comp a
  let R := b.range
  let b' : S.toRepresentation.IntertwiningMap R.toRepresentation := {
    toLinearMap := b.toLinearMap.rangeRestrict
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro s
      apply Subtype.ext
      exact LinearMap.congr_fun (b.isIntertwining' g) s }
  have hb' : Function.Surjective b' := by
    rintro ⟨z, v, hv⟩
    exact ⟨v, Subtype.ext hv⟩
  have hk : b'.ker ≤ f.ker := by
    intro v hv
    have hb : b v = 0 := congrArg Subtype.val hv
    have hvN : a v ∈ N := (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp hb
    have hvT : (v : V) ∈ T := ⟨a v, hvN, rfl⟩
    have he := congrArg (fun l : K.toRepresentation.IntertwiningMap σ => l ⟨v, v.property, hvT⟩) hz
    exact he
  obtain ⟨p, hp⟩ := factor_surjection b' hb' f hf hk
  exact section_iff_surjection.mpr ⟨hs.1, R, p, hp⟩

end SectionReduction
end Representation.QuadraticFourGroup

end
