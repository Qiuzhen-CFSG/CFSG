module

public import Theory.Representation.QuadraticFourGroup.CubicSections.SplitSection
public import Theory.Representation.QuadraticFourGroup.CubicSections.Descent
public import Theory.Representation.QuadraticFourGroup.CubicSections.SectionReduction.Setup
public import Theory.Representation.QuadraticFourGroup.CubicSections.SectionReduction.ImageHypotheses
public import Theory.Representation.QuadraticFourGroup.CubicSections.SectionReduction.Occurrence
public import Theory.Representation.QuadraticFourGroup.CubicSections.SectionReduction.KernelMarking

/-!
# Faithful split actions from ambient irreducible sections

Every nontrivial irreducible section of the action of `E = ⟨L^B⟩` occurs
in the restriction of an actual irreducible subquotient for `X = L ⊔ B`.
Its kernel on `E` is precisely `O₂(E)`, so the supplied two-factor model
embeds in the faithful kernel quotient. A marking of its first factor by
a surviving `B`-conjugate of `L` transports every source hypothesis to
that quotient. The component orbit is exactly the embedded product, and
the prescribed descended section occurs in the restricted faithful
irreducible action.

`splitSectionWitness_of_lift` constructs all fields of the witness from
an ambient section, exact kernel and factor marking.
`exists_splitSectionWitness` supplies those inputs for every prescribed
nontrivial section, retaining the supplied model's quotient equivalence.
Source: GLS, volume 2, Theorem 25.14, Step 2, with Clifford restriction.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
universe u v w z

namespace Representation.QuadraticFourGroup.SectionReduction
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {U : Type z} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {W : Type w} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {L B : Subgroup G} {a : G}

/-- Assemble the faithful split action from an actual ambient section and
the exact kernel and component marking in the supplied model. -/
theorem splitSectionWitness_of_lift
    (h : Hypotheses ρ L B a) (M : TwoFactorModel (componentOrbit L B))
    (τ : Representation (ZMod 2) (L ⊔ B : Subgroup G) U) [τ.IsIrreducible]
    (hsX : IsIrreducibleSection (ρ.comp (L ⊔ B).subtype) τ)
    (σ : Representation (ZMod 2) (componentOrbit L B) W)
    (hsE : IsIrreducibleSection (τ.comp (orbitInclusion L B)) σ)
    (hker : (τ.comp (orbitInclusion L B)).ker = pCore 2 (componentOrbit L B))
    (b : B.subgroupOf (L ⊔ B))
    (hfirst :
      ((embedding (orbitInclusion L B) τ M (orbit_twoCore_le_ker L B τ)).comp
        (MonoidHom.inl (Factor M.n) (Factor M.n))).range =
      ((L.subgroupOf (L ⊔ B)).map (MulAut.conj (b : (L ⊔ B : Subgroup G))).toMonoidHom).map
        (QuotientGroup.mk' τ.ker))
    (hsurv :
      ((L.subgroupOf (L ⊔ B)).map (MulAut.conj (b : (L ⊔ B : Subgroup G))).toMonoidHom).map
        (QuotientGroup.mk' τ.ker) ≠ ⊥) :
    letI := hsE.1
    Nonempty (SplitSectionWitness.{u, z, w} (M.sectionRepresentation σ)) := by
  let := hsE.1
  let q := QuotientGroup.mk' τ.ker
  let j := embedding (orbitInclusion L B) τ M (orbit_twoCore_le_ker L B τ)
  have hlocal := (h.restrictOvergroup le_sup_left le_sup_right).conjugate_component b
  have himage := hlocal.faithful_section_image q (QuotientGroup.mk'_surjective _)
    (kerRepresentation τ) (kerRepresentation_faithful τ) hsX hsurv
  let d : SplitOrbit (kerRepresentation τ) M.n := {
    one_lt := M.one_lt
    embedding := j
    injective := embedding_injective (orbitInclusion L B) τ M
      (orbit_twoCore_le_ker L B τ) hker
    fourGroup := (B.subgroupOf (L ⊔ B)).map q
    involution := q ⟨a, (le_sup_right : B ≤ L ⊔ B) h.mem⟩
    hypotheses := by
      change Hypotheses (kerRepresentation τ)
        ((embedding (orbitInclusion L B) τ M (orbit_twoCore_le_ker L B τ)).comp
          (MonoidHom.inl (Factor M.n) (Factor M.n))).range _ _
      rw [hfirst]
      exact himage
    orbit_eq := by
      change componentOrbit
        ((embedding (orbitInclusion L B) τ M (orbit_twoCore_le_ker L B τ)).comp
          (MonoidHom.inl (Factor M.n) (Factor M.n))).range
        ((B.subgroupOf (L ⊔ B)).map q) = j.range
      rw [hfirst, ← componentOrbit_map, orbit_conjugate_component,
        localOrbit_eq_range, MonoidHom.map_range]
      exact (M.liftTo_range _ _).symm
  }
  exact ⟨{
    Actor := (L ⊔ B : Subgroup G) ⧸ τ.ker
    Space := U
    action := kerRepresentation τ
    irreducible := inferInstance
    split := d
    isSection := faithfulAction_isSection (orbitInclusion L B) τ M
      (orbit_twoCore_le_ker L B τ) σ hsE
  }⟩

/-- Every prescribed nontrivial irreducible orbit section occurs in a faithful
irreducible split action with the original two-factor model. No irreducibility
of the original action or faithfulness of the prescribed section is assumed. -/
theorem exists_splitSectionWitness [FiniteDimensional (ZMod 2) V]
    (h : Hypotheses ρ L B a) (M : TwoFactorModel (componentOrbit L B))
    (σ : Representation (ZMod 2) (componentOrbit L B) W)
    (hs : IsIrreducibleSection (ρ.comp (componentOrbit L B).subtype) σ)
    (hn : ¬ σ.IsTrivial) :
    letI := hs.1
    Nonempty (SplitSectionWitness.{u, v, w} (M.sectionRepresentation σ)) := by
  let := hs.1
  obtain ⟨U, N, hτ, hsE⟩ := exists_irreducible_section_occurrence
    (ρ.comp (L ⊔ B).subtype) (orbitInclusion L B) σ hs
  let := hτ
  have hsX : IsIrreducibleSection (ρ.comp (L ⊔ B).subtype)
      N.quotientRepresentation := ⟨hτ, U, N, ⟨Representation.Equiv.refl _⟩⟩
  have hnE : ¬ Representation.IsTrivial
      (N.quotientRepresentation.comp (orbitInclusion L B)) :=
    fun ht => hn (hsE.isTrivial ht)
  obtain ⟨b, hfirst, hsurv⟩ := exists_embedding_component_marking h M
    N.quotientRepresentation hnE
  exact splitSectionWitness_of_lift h M N.quotientRepresentation hsX σ hsE
    (orbit_ker_eq_twoCore h M N.quotientRepresentation hnE) b hfirst hsurv

end Representation.QuadraticFourGroup.SectionReduction

end
