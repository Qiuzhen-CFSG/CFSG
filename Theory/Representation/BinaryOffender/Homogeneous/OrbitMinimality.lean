module
public import Theory.Representation.BinaryOffender.Homogeneous.OrbitConsequences
/-!
# Minimality of homogeneous binary orbits

A subrepresentation invariant under the orbit action is either zero or the
whole orbit of a homogeneous simple seed. Pulling this statement through
the central quotient gives minimality modulo the original fixed space for
an Irr⁺ seed. Full commutator generation recovers equality before quotienting.

Source: Aschbacher--Smith D.3.4 and D.3.6, printed pp.195--196.
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup
open scoped MonoidAlgebra
namespace Representation.BinaryOffender.Homogeneous

private theorem simple_type_in_span
    {E W P : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W] [Group P]
    {σ : Representation (ZMod 2) E W} (c : TypeAction σ P)
    (S : Subrepresentation σ) (hS : IsIrreducible S.toRepresentation)
    (A : Subrepresentation σ) (hA : IsIrreducible A.toRepresentation)
    (hAS : A ≤ c.span S) : ∃ t : P, SameModule A (c.conjugate t S) := by
  classical
  by_contra! hn
  let := simple_asSubmodule A hA
  have hd := component_disjoint_sum A.asSubmodule
    (fun t => (c.conjugate t S).asSubmodule)
    (fun t => simple_asSubmodule _ (c.conjugate_irreducible S hS t))
    (fun t he => hn t ((sameModule_iff_linearEquiv _ _).mpr he))
  have hle : A.asSubmodule ≤ ⨆ t : P, (c.conjugate t S).asSubmodule := by
    have h := Subrepresentation.subrepresentationSubmoduleOrderIso.monotone hAS
    simpa only [TypeAction.span, OrderIso.map_iSup,
      Subrepresentation.subrepresentationSubmoduleOrderIso_apply] using h
  have hz : A.asSubmodule = ⊥ :=
    le_bot_iff.mp ((le_inf A.asSubmodule.le_isotypicComponent hle).trans_eq hd.eq_bot)
  exact ((Subrepresentation.irreducible_iff_isAtom A).mp hA).ne_bot
    (Subrepresentation.subrepresentationSubmoduleOrderIso.injective
      (hz.trans Subrepresentation.subrepresentationSubmoduleOrderIso.map_bot.symm))

/-- A homogeneous simple orbit has no proper nonzero invariant subrepresentation. -/
theorem TypeAction.eq_bot_or_eq_span_of_invariant
    {E W P : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] [Group P] {σ : Representation (ZMod 2) E W}
    (c : TypeAction σ P) (S : Subrepresentation σ)
    (hS : IsIrreducible S.toRepresentation)
    (hh : homogeneousPart S (c.span S).toSubmodule = S.toSubmodule)
    (Q : Subrepresentation σ) (hQ : Q ≤ c.span S)
    (hfix : ∀ t : P, c.conjugate t Q = Q) : Q = ⊥ ∨ Q = c.span S := by
  let : Finite (Subrepresentation σ) := Finite.of_injective
    Subrepresentation.toSubmodule Subrepresentation.toSubmodule_injective
  rcases eq_bot_or_exists_atom_le Q with hz | ⟨A,hA,hAQ⟩
  · exact Or.inl hz
  right
  have hi := (Subrepresentation.irreducible_iff_isAtom A).mpr hA
  obtain ⟨t,ht⟩ := simple_type_in_span c S hS A hi (hAQ.trans hQ)
  have he : SameModule S (c.conjugate t⁻¹ A) := by
    have h := (c.same t⁻¹ A (c.conjugate t S)).mp ht
    rw [c.inv_conjugate] at h
    exact h.symm
  have hAQ' : c.conjugate t⁻¹ A ≤ Q := (c.conjugate t⁻¹).monotone hAQ |>.trans_eq (hfix _)
  have hAS : c.conjugate t⁻¹ A ≤ S := by
    change (c.conjugate t⁻¹ A).toSubmodule ≤ S.toSubmodule
    rw [←hh]
    exact le_iSup_of_le _ (le_iSup_of_le ⟨hAQ'.trans hQ,he⟩ le_rfl)
  have hAS' : c.conjugate t⁻¹ A = S :=
    ((Subrepresentation.irreducible_iff_isAtom S).mp hS).le_iff_eq
      ((Subrepresentation.irreducible_iff_isAtom _).mp
        (c.conjugate_irreducible A hi t⁻¹)).ne_bot |>.mp hAS
  have hSQ : S ≤ Q := hAS' ▸ hAQ'
  apply le_antisymm hQ
  exact iSup_le fun t => (c.conjugate t).monotone hSQ |>.trans_eq (hfix t)

/-- Minimality under the original actor and orbit group, with the full central layer retained. -/
theorem IsIrrPlusWith.eq_or_le_fixedSpace_of_invariant
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) {X T : Subgroup G}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ X T I)
    (J : Submodule (ZMod 2) V) (hJ : J ≤ orbitSpan ρ T I)
    (hXJ : X ≤ subspaceStabilizer ρ J) (hTJ : T ≤ subspaceStabilizer ρ J) :
    J = orbitSpan ρ T I ∨ J ≤ fixedSpace ρ X := by
  let : Finite (V ⧸ fixedSpace ρ X) := Finite.of_surjective _ (Submodule.mkQ_surjective (fixedSpace ρ X))
  let c := centralTypeAction ρ X T hI.normalizes
  let S := quotientImage ρ X I hI.invariant
  let Q := quotientImage ρ X J hXJ
  have hs : (c.span S).toSubmodule = (orbitSpan ρ T I).map (fixedSpace ρ X).mkQ := by
    rw [centralTypeAction_span]
    exact (orbitSpan_quotientImage ρ X T hI.normalizes I).symm
  have hh : homogeneousPart S (c.span S).toSubmodule = S.toSubmodule := by
    rw [hs]
    exact hI.homogeneous
  have hQ : Q ≤ c.span S := by
    change J.map (fixedSpace ρ X).mkQ ≤ (c.span S).toSubmodule
    rw [hs]
    exact Submodule.map_mono hJ
  have hfix (t : T) : c.conjugate t Q = Q := by
    apply Subrepresentation.toSubmodule_injective
    rw [centralConjugate_toSubmodule]
    change (J.map (fixedSpace ρ X).mkQ).map
      (normalizerQuotientRepresentation ρ X ⟨t,hI.normalizes t.property⟩) = _
    rw [←quotientImage_map_normalizer,
      (subspace_map_eq_iff ρ J (t : G)).mpr (hTJ t.property)]
    rfl
  rcases c.eq_bot_or_eq_span_of_invariant S (quotientImage_irreducible ρ hI.isIrrPlus)
      hh Q hQ hfix with hz | he
  · right
    intro v hv
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have h : (fixedSpace ρ X).mkQ v ∈ Q := ⟨v,hv,rfl⟩
    rw [hz] at h
    exact h
  · left
    apply le_antisymm hJ
    apply le_of_quotientImage_le ρ (orbitSpan_full_commutator ρ hI.normalizes hI.isIrrPlus) hXJ
    rw [←hs,←he]
    exact le_rfl
end Representation.BinaryOffender.Homogeneous
