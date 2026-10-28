module
public import Theory.Representation.BinaryOffender.RestrictedConstituent
public import Theory.Representation.BinaryOffender.SchurNormalizerDisplacement
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.RestrictionComparison

/-!
# Schur linearity of small-displacement constituents

The stabilizer of a normal-subgroup constituent acts in the literal linear
normalizer of its representation. If the actor's displacement is smaller
than half the constituent dimension, this action commutes with every Schur
endomorphism: a nontrivial action on the Schur field would move at least
half the space.

The Chapter 10 Suzuki-pair application uses the actual restricted actor
and its proved invariant constituent. No linearity over the endomorphism
field is assumed.
Source: Aschbacher--Smith D.3.7--9, printed pp.197--201; the Schur-field
estimate is the scalar/semilinear distinction in Guralnick--Malle,
Classification of 2F-modules II, Section 3.5, manuscript p.20.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The literal constituent-stabilizer action lies in its linear normalizer. -/
def constituentNormalizerHom (X : Subgroup G) [X.Normal]
    (U : Subrepresentation (ρ.comp X.subtype)) :
    subspaceStabilizer ρ U.toSubmodule →* linearNormalizer U.toRepresentation :=
  (stabilizerRepresentation ρ U.toSubmodule).asGroupHom.codRestrict _ (by
    intro b
    let S := subspaceStabilizer ρ U.toSubmodule
    let P := X.subgroupOf S
    let τ := stabilizerRepresentation ρ U.toSubmodule
    have hXU : X ≤ S := le_subspaceStabilizer ρ _
      (fun x hx v hv => U.apply_mem_toSubmodule ⟨x,hx⟩ hv)
    have he : actionImage (τ.comp P.subtype) = actionImage U.toRepresentation := by
      ext z
      constructor
      · rintro ⟨x,rfl⟩
        exact ⟨⟨x.val.val,x.property⟩,Units.ext rfl⟩
      · rintro ⟨x,rfl⟩
        exact ⟨⟨⟨x,hXU x.property⟩,x.property⟩,Units.ext rfl⟩
    change τ.asGroupHom b ∈ normalizer (actionImage U.toRepresentation : Set _)
    rw [←he]
    exact actionImage_le_linearNormalizer τ P ⟨b,rfl⟩)

/-- A strict half-dimension displacement bound forces Schur linearity. -/
theorem constituent_schurLinear_of_small_restricted_codim
    [FiniteDimensional (ZMod 2) V]
    (X : Subgroup G) [X.Normal]
    (U : Subrepresentation (ρ.comp X.subtype)) (hU : U.toRepresentation.IsIrreducible)
    (A : Subgroup G)
    (hsmall : 2 * fixedCodim (subspaceImageRepresentation ρ U.toSubmodule)
      (restrictedSubgroup ρ U.toSubmodule A) < Module.finrank (ZMod 2) U.toSubmodule) :
    ∀ b : subspaceStabilizer ρ U.toSubmodule, (b : G) ∈ A →
      ∀ (f : IntertwiningMap U.toRepresentation U.toRepresentation) (v : U.toSubmodule),
        stabilizerRepresentation ρ U.toSubmodule b (f v) =
          f (stabilizerRepresentation ρ U.toSubmodule b v) := by
  intro b hb
  change SchurNormalizer.IsSchurLinear U.toRepresentation (constituentNormalizerHom ρ X U b)
  by_contra hnot
  let := hU
  have hlo := SchurNormalizer.finrank_le_twice_fixedCodim U.toRepresentation
    (constituentNormalizerHom ρ X U b) hnot
  let τ := subspaceImageRepresentation ρ U.toSubmodule
  let B := restrictedSubgroup ρ U.toSubmodule A
  let b' := subspaceActionHom ρ U.toSubmodule b
  have hb' : b' ∈ B := ⟨b,hb,rfl⟩
  have he : fixedCodim (normalizerRepresentation U.toRepresentation)
      (zpowers (constituentNormalizerHom ρ X U b)) = fixedCodim τ (zpowers b') := by
    simp only [fixedCodim_zpowers_eq_displacement_rank]
    rfl
  rw [he] at hlo
  have hm := Submodule.finrank_mono (fixedSpace_antitone τ (zpowers_le.mpr hb'))
  have hdB := fixedCodim_add_finrank τ B
  have hdb := fixedCodim_add_finrank τ (zpowers b')
  change 2 * fixedCodim τ B < Module.finrank (ZMod 2) U.toSubmodule at hsmall
  omega
end Representation.BinaryOffender
