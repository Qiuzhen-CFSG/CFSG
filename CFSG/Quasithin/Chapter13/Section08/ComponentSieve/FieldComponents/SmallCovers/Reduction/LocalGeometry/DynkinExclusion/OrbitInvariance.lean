module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance.Inputs

/-!
# An invariant faithful irreducible constituent for the cubic cover

F.9.18(4i),(4ii) give invariance of the chosen homogeneous Irr⁺ member.
Alternative (4iii) is impossible: SL₃ in characteristic two contains SL₃(2),
whose order does not divide 1080, and the other listed groups have trivial
center, whereas the actual triple cover has center of order three. The cubic
polynomial removes all central fixed vectors, so the Irr⁺ quotient is the
original section. The component-centralizer bound then proves faithfulness.
Finally the elementary quadratic subgroup in F.9.18(3)'s action image lifts
along this faithful action, with unchanged rank and fixed codimension.

Homogeneous existence and the universal earlier F.9 statements remain with
the source assembly. No B.4 classification is applied here, and no relation
between Y and L₁ is assumed. This is the intermediate passage needed before
the parent applies the irreducible B.4.5 input.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), F.9.18(3),(4),
printed pp.325–326; 13.8.21(2), printed p.956.
-/

@[expose] public section

open Representation Representation.BinaryOffender Subgroup
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal]
  (P : Sylow 2 D) (hgen : L ⊔ (P : Subgroup D) = ⊤)

omit [L.Normal] in
/-- Exclusion uses the actual group models, including the SL₃ alternative
whose center can also have order three. -/
theorem not_hattedNaturalPair (e : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlusWith ρ L P I) :
    ¬ HattedNaturalPair ρ L P I hI := by
  intro h
  apply hex_not_pairCarrier
  apply PairCarrier.of_equiv e.symm
  rcases h.model with h | ⟨h, _⟩
  · exact h.pairCarrier
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- P-invariance of the chosen constituent follows from all three source
alternatives, before applying an irreducible representation classification. -/
theorem invariant (e : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (src : OrbitInputs ρ L P hgen)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlusWith ρ L P I) :
    (P : Subgroup D) ≤ subspaceStabilizer ρ I := by
  rcases src.alternatives I hI with h | ⟨h, _⟩ | h
  · exact le_top.trans h
  · rw [← h]
    exact orbitSpan_invariant ρ P I
  · exact (not_hattedNaturalPair ρ L P e I hI h).elim

/-- The literal invariant subspace, faithful and L-irreducible, with the
ratio bound transported from its actual orbit action image. -/
theorem exists_faithful_irreducible_section [Finite D] [FiniteDimensional (ZMod 2) V]
    (e : L ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hcent : centralizer (L : Set D) ≤ L)
    (z : D) (hzorder : orderOf z = 3)
    (hzcenter : zpowers z = (center L).map L.subtype)
    (hp : CubicPolynomial ρ z)
    (src : OrbitInputs ρ L P hgen)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlusWith ρ L P I) :
    ∃ J : Subrepresentation ρ, J.toSubmodule = I ∧
      Function.Injective J.toRepresentation ∧
      Representation.IsIrreducible (J.toRepresentation.comp L.subtype) ∧
      quadraticRatio J.toRepresentation ≤ 2 := by
  have hzL : z ∈ L := by
    have hz := mem_zpowers z
    rw [hzcenter] at hz
    obtain ⟨w, _, rfl⟩ := hz
    exact w.property
  have hcz : centralizer (L : Set D) ≤ zpowers z := by
    rw [hzcenter]
    intro x hx
    refine ⟨⟨x, hcent hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro l
    apply Subtype.ext
    exact mem_centralizer_iff.mp hx l l.property
  let : Theory.GroupTheory.IsQuasisimple Atlas.Codes.HexEvenAutomorphisms :=
    Hexacode.even_isQuasisimple
  let : Theory.GroupTheory.IsQuasisimple L :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv e.symm
  let J := orbitSubrepresentation ρ hI.normalizes hI.isIrrPlus hgen
  have heq : J.toSubmodule = I :=
    orbitSpan_eq_self ρ (invariant ρ L P hgen e src I hI)
  have hn : J ≠ ⊥ := by
    intro h
    apply hI.isIrrPlus.ne_bot ρ
    rw [← heq, h]
    rfl
  have hf : Function.Injective J.toRepresentation :=
    faithful_subrepresentation_of_cubicPolynomial ρ L z hzL hzorder hcz hp J hn
  refine ⟨J, heq, hf, ?_, ratio_of_image J.toRepresentation hf (src.ratio I hI).1⟩
  have hi : IsIrrPlus ρ L J.toSubmodule := heq.symm ▸ hI.isIrrPlus
  exact irreducible_of_cubic ρ L z hzL hp J.toSubmodule hi

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
