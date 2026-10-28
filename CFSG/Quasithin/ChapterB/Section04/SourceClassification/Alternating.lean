module

public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.BinaryFour
public import CFSG.Quasithin.ChapterB.Section04.SourceClassification.RankOne
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.SourceAssembly
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# The complete alternating family of B.4.2

The source central quotient is perfect, excluding degrees below five by
the solvability of S₄. The actual A₅–PSL₂(4) comparison supplies the rank-one
branch; A₆ and A₇ use the complete FF recognition and offender calculations;
A₈ uses binary SL₄ recognition, retaining its natural and orthogonal modules
and all permitted symmetric extensions.

This discharges the entire alternating constructor of the literal Theorem C
catalogue, whose statement includes every degree at most eight.
Source: Aschbacher–Smith B.4.2, K.1, K.3.1 and K.3.2.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceClassification
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The source perfect central quotient rules out all small solvable degrees. -/
theorem alternating_degree_ge_five (h : ChapterK.RankOne.SourceHypotheses ρ L)
    {n : ℕ} (e : L ⧸ center L ≃* alternatingGroup (Fin n)) : 5 ≤ n := by
  let := h.quasisimple
  let S := L ⧸ center L
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center L))
  let : IsSimpleGroup S := IsQuasisimple.simple
  by_contra! hn
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let f := (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb (by omega : n ≤ 4))).comp
    ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom)
  have hf : Function.Injective f :=
    (Equiv.Perm.viaEmbeddingHom_injective _).comp (Subtype.val_injective.comp e.injective)
  exact Group.IsPerfect.not_isSolvable S (Group.isSolvable_of_isSolvable_injective hf)

/-- The A₅ branch uses the actual projective action over the four-element field. -/
theorem alternating_five_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) (e : L ⧸ center L ≃* alternatingGroup (Fin 5)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  apply psl2_case h hff (r := 2) (by decide)
  exact ⟨GaloisField 2 2,inferInstance,inferInstance,
    GaloisField.card 2 2 (by decide),⟨e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩

/-- Every alternating central quotient allowed by Theorem C gives its actual
corrected B.4.2 action row, including all module and ambient alternatives. -/
theorem alternating_case (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ) {n : ℕ} (hn : n ≤ 8)
    (e : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  have hlo := alternating_degree_ge_five h e
  have hcases : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact alternating_five_case h hff e
  · exact (ChapterK.Alternating.source_of_ff_input ρ
      ⟨h.sqtk,h.fitting.symm,h.quasisimple,h.faithful,h.irreducible,h.smallCubic,
        Or.inl ⟨e⟩⟩ hff).2
  · exact (ChapterK.Alternating.source_of_ff_input ρ
      ⟨h.sqtk,h.fitting.symm,h.quasisimple,h.faithful,h.irreducible,h.smallCubic,
        Or.inr ⟨e⟩⟩ hff).2
  · exact alternating_eight_case h e

/-- Literal source application to the full alternating catalogue constructor. -/
theorem alternating_of_bestOffender (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (hfit : generalizedFitting G = L) (hL : IsQuasisimple L)
    (hf : Function.Injective ρ) (hi : IsIrreducible (ρ.comp L.subtype))
    {A : Subgroup G} (hA : IsBestOffender ρ A) {n : ℕ} (hn : n ≤ 8)
    (e : L ⧸ center L ≃* alternatingGroup (Fin n)) :
    SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) :=
  alternating_case (source_hypotheses_of_bestOffender hsq hfit hL hf hi hA)
    ⟨A,hA.isOffender ρ⟩ hn e

end CFSG.Quasithin.ChapterB.SourceClassification
