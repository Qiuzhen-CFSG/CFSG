module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialityPresentation.SignedSubgroup
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.BruhatCollection

/-!
# The triality presentation cover on the literal source quotient

The full explicit signed-root relations give a Bruhat cover of `X / Q.D`.
The generated Borel normalizes the original source U, so the two factors in
this cover belong to the complete source Borel, by `SplitData.normalizer_eq`.
The original scalar marking, quotient map, and representatives are unchanged.
The numerator may be an original group or a geometric completion; no descent
from the latter to the former is assumed.

This is a conditional application of abstract collection, not a triality
recognition theorem. Concrete presentation faithfulness and both marked
parabolics remain necessary. The source owner must construct all input equations.
Source: GLS3 2.3.5, 2.4.7–8; DGS Theorem D, printed p.224.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation
variable {X F : Type*} [Group X] [Field F] {Psrc : Fin 2 → Subgroup X}
variable {Q : MarkedQuotient Psrc} {split : SplitData Q.tits}
variable {m : ℕ} {hm : 0 < m} {σ : F ≃+* F}

/-- Source fields, signed roots, all explicit equations, and generation.
No model map, group order, simplicity or normal-form faithfulness is input. -/
structure BruhatRootData (d : PositiveRootData Q split m hm σ) where
  signed : SignedRootData d
  weyl : signed.roots.WeylRelations
  torus : signed.roots.TorusRelations
  generates : signed.roots.signedClosure = ⊤

namespace BruhatRootData
variable {d : PositiveRootData Q split m hm σ} (b : BruhatRootData d)

/-- The source equations instantiate the full map-free presentation contract. -/
theorem relations : b.signed.roots.Relations :=
  { b.weyl, b.signed.actions, b.torus with }

/-- The entire collected Borel lies in the actual source Borel, by its
normalizer characterization. This includes every torus root word. -/
theorem borel_le_source : b.signed.roots.borel b.relations ≤ Q.tits.B := by
  have h := b.signed.roots.borel_le_normalizer b.relations
  have hp : b.signed.roots.positive.positiveClosure = split.U := d.positive
  rw [hp, split.normalizer_eq] at h
  exact h

/-- Bruhat coverage on the literal X/Q.D, for either original or geometric
numerator. Both Borel factors belong to the complete source Borel. -/
theorem source_bruhat (g : X ⧸ Q.D) :
    ∃ (u v : X ⧸ Q.D) (a : Bool) (k : ℕ),
      u ∈ Q.tits.B ∧ v ∈ Q.tits.B ∧ k ≤ 6 ∧
      g = u * b.signed.roots.alternating a k * v := by
  obtain ⟨u,v,a,k,hu,hv,hk,he⟩ := b.signed.roots.bruhat_collection b.relations
    (g := g) (b.generates ▸ Subgroup.mem_top g)
  exact ⟨u,v,a,k,b.borel_le_source hu,b.borel_le_source hv,hk,he⟩

/-- Retain the original quotient projection and every original representative. -/
theorem original_bruhat (x : X) :
    ∃ (u v : X ⧸ Q.D) (a : Bool) (k : ℕ),
      u ∈ Q.tits.B ∧ v ∈ Q.tits.B ∧ k ≤ 6 ∧
      Q.q x = u * b.signed.roots.alternating a k * v :=
  b.source_bruhat (Q.q x)

include b in
/-- Finiteness follows from the presentation, independently of source finiteness. -/
theorem quotient_finite : Finite (X ⧸ Q.D) :=
  SignedRoots.finite_of_generated b.signed.roots b.relations b.generates

end BruhatRootData
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation
