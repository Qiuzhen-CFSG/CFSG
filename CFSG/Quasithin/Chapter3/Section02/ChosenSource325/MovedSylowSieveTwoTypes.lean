module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveTwists
public import Theory.Representation.BinaryOffender.Homogeneous.QuotientOrbitModels

/-!
# Two literal homogeneous conjugates from two automorphism types

A characteristic quotient model assigns each central constituent one of two
unchanged-actor module types. Homogeneity identifies constituents of the same
type; full commutator generation lifts those equalities through the central
quotient. Thus a moved seed has exactly two actual conjugates, without any
assumed bound on their multiplicities. The Chapter 12 consumer is
`SeedAlternativesMovedSylowTwoTypes`.

Source: Aschbacher--Smith A.1.42 and D.3.5(4), combined manuscript of
1 March 2004, printed pp.32 and195--196.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {G V P W : Type*} [Group G] [Group P]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V)

/-- Two automorphism types on the characteristic quotient exhaust the literal
orbit of a moved homogeneous full-commutator seed. -/
theorem homogeneous_two_conjugates_of_quotient_twists
    {X T : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ X T I)
    (N : Subgroup X) [N.Characteristic] (q : (X ⧸ N) ≃* P)
    (τ₀ τ₁ : Representation (ZMod 2) P W)
    (b : (quotientImage ρ X I hI.invariant).toRepresentation.Equiv
      (τ₀.comp (q.toMonoidHom.comp (QuotientGroup.mk' N))))
    (hm : ∃ t : T, I.map (ρ t.val) ≠ I)
    (htypes : ∀ a : MulAut P, Nonempty (Representation.Equiv (τ₀.comp a.toMonoidHom) τ₀) ∨
      Nonempty (Representation.Equiv (τ₀.comp a.toMonoidHom) τ₁)) :
    ∃ t : T, I.map (ρ t.val) ≠ I ∧
      ∀ s : T, I.map (ρ s.val) = I ∨ I.map (ρ s.val) = I.map (ρ t.val) := by
  let c := centralTypeAction ρ X T hI.normalizes
  let S := quotientImage ρ X I hI.invariant
  let f := q.toMonoidHom.comp (QuotientGroup.mk' N)
  have hh : homogeneousPart S (c.span S).toSubmodule = S.toSubmodule := by
    rw [centralTypeAction_span]
    exact hI.central_homogeneous ρ
  have hi := quotientImage_irreducible ρ hI.isIrrPlus
  have hJ (s : T) := hI.isIrrPlus.map_normalizer ρ (hI.normalizes s.property)
  have hconj (s : T) : c.conjugate s S =
      quotientImage ρ X (I.map (ρ s.val)) (hJ s).choose := by
    apply Subrepresentation.toSubmodule_injective
    rw [centralConjugate_toSubmodule]
    exact (quotientImage_map_normalizer ρ X I ⟨s.val,hI.normalizes s.property⟩).symm
  have hlift (s t : T) (he : c.conjugate s S = c.conjugate t S) :
      I.map (ρ s.val) = I.map (ρ t.val) := by
    rw [hconj s,hconj t] at he
    have he' := congrArg Subrepresentation.toSubmodule he
    exact le_antisymm
      (le_of_quotientImage_le ρ (hJ s).choose_spec.1 (hJ t).choose he'.le)
      (le_of_quotientImage_le ρ (hJ t).choose_spec.1 (hJ s).choose he'.ge)
  have hmodels (s : T) :
      Nonempty ((c.conjugate s S).toRepresentation.Equiv (τ₀.comp f)) ∨
      Nonempty ((c.conjugate s S).toRepresentation.Equiv (τ₁.comp f)) := by
    obtain ⟨a,⟨ea⟩⟩ := hI.centralConjugate_equiv_quotient_twist ρ s N q τ₀ b
    rcases htypes a with h | h
    · obtain ⟨d⟩ := h
      exact Or.inl ⟨ea.trans (Representation.Equiv.mk d.toLinearEquiv (by
        intro x; apply LinearMap.ext; intro v
        exact IntertwiningMap.isIntertwining _ _ d.toIntertwiningMap (f x) v))⟩
    · obtain ⟨d⟩ := h
      exact Or.inr ⟨ea.trans (Representation.Equiv.mk d.toLinearEquiv (by
        intro x; apply LinearMap.ext; intro v
        exact IntertwiningMap.isIntertwining _ _ d.toIntertwiningMap (f x) v))⟩
  have heq (s t : T) (τ : Representation (ZMod 2) X W)
      (es : (c.conjugate s S).toRepresentation.Equiv τ)
      (et : (c.conjugate t S).toRepresentation.Equiv τ) :
      I.map (ρ s.val) = I.map (ρ t.val) := by
    let e := es.trans et.symm
    exact hlift s t (c.conjugate_eq_of_sameModule S hi hh s t
      ⟨e.toLinearEquiv,fun x v => IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap x v⟩)
  have eone : (c.conjugate 1 S).toRepresentation.Equiv (τ₀.comp f) := by
    rw [c.one]
    exact b
  obtain ⟨t,ht⟩ := hm
  obtain ⟨et⟩ : Nonempty ((c.conjugate t S).toRepresentation.Equiv (τ₁.comp f)) := by
    rcases hmodels t with h | h
    · obtain ⟨et⟩ := h
      exact (ht (by simpa only [Subgroup.coe_one,map_one,Module.End.one_eq_id,
        Submodule.map_id] using heq t 1 _ et eone)).elim
    · exact h
  refine ⟨t,ht,fun s => ?_⟩
  rcases hmodels s with h | h
  · obtain ⟨es⟩ := h
    exact Or.inl (by simpa only [Subgroup.coe_one,map_one,Module.End.one_eq_id,
      Submodule.map_id] using heq s 1 _ es eone)
  · obtain ⟨es⟩ := h
    exact Or.inr (heq s t _ es et)

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
