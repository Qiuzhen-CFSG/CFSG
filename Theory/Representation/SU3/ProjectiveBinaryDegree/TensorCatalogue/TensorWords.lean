module

public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.Representation.Quotient
public import Theory.Representation.SL3.BinaryDefiningFactors.SmallPatterns

/-!
# The actual unitary tensor words

The four restricted factors for type A₂ are restricted along the literal
inclusion of the full special unitary group into SL₃ of the matrix field.
The word has length s, although that field has order 2^(2s). Simplicity and
exhaustiveness after this restriction are separate obligations: neither follows
by restricting the SL₃ classification. The single-factor comparison here merely
restricts an already constructed intertwiner.

Source: GLS III, §2.8; Guralnick--Malle, Theorem 4.10, first paragraph.
Reused from `CFSG/Quasithin/ChapterK/Section01To04/RankOne/UnitaryRecognition/MinimalDegree/TensorWords.lean`, with the original
proofs retained in a reusable Theory namespace for Fong--Seitz I (4D).
-/

@[expose] public noncomputable section
namespace Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue
open BenderSuzuki.MatrixGroups Representation
open Representation.SL3.BinaryDefiningFactors
open scoped MatrixGroups

variable {F K : Type*} [Field F] [Field K]

/-- Forget the unitary equation, retaining the same determinant-one matrix. -/
def specialLinearInclusion (J : HermitianForm 3 F) : J.specialSubgroup →* SL(3,F) where
  toFun g := ⟨g.val.val, congrArg Units.val
    ((J.mem_specialSubgroup_iff g.val).mp g.property).2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem specialLinearInclusion_injective (J : HermitianForm 3 F) :
    Function.Injective (specialLinearInclusion J) := by
  intro g k h
  exact Subtype.ext (Units.ext (congrArg Subtype.val h))

/-- The coefficient-embedded natural action of the full special unitary group. -/
def natural (J : HermitianForm 3 F) (ι : F →+* K) :
    Representation K J.specialSubgroup (Fin 3 → K) :=
  (Representation.SL3.BinaryDefiningFactors.natural ι).comp (specialLinearInclusion J)

theorem natural_apply (J : HermitianForm 3 F) (ι : F →+* K)
    (g : J.specialSubgroup) (v : Fin 3 → K) :
    natural J ι g v = Matrix.mulVec (g.val.val.map ι) v := rfl

/-- Restriction of the concrete tensor word. This definition asserts no
irreducibility or extension theorem for arbitrary unitary representations. -/
def word [CharP K 2] (J : HermitianForm 3 F) (ι : F →+* K) (w : List Factor) :
    Representation K J.specialSubgroup (WordSpace K w) :=
  (wordRep ι w).comp (specialLinearInclusion J)

/-- Restrict an actual representation equivalence along any group map. -/
def restrictEquiv {G H U W : Type*} [Group G] [Group H]
    [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    {ρ : Representation K G U} {τ : Representation K G W}
    (π : H →* G) (e : ρ.Equiv τ) : Representation.Equiv (ρ.comp π) (τ.comp π) :=
  .mk e.toLinearEquiv (fun g => e.isIntertwining' (π g))

/-- A singleton word retains its coefficient twist and its duality label.
The conclusion supplies genuine equivalences of representations. -/
theorem word_single_factor [CharP K 2]
    (J : HermitianForm 3 F) (ι : F →+* K) (w : List Factor)
    (hn : naturalCount w = 1) (ha : adjointCount w = 0) :
    ∃ ι' : F →+* K,
      Nonempty ((word J ι w).Equiv (natural J ι')) ∨
      Nonempty ((word J ι w).Equiv (natural J ι').dual) := by
  obtain ⟨ι', h | h⟩ := wordRep_single_factor ι w hn ha
  · exact ⟨ι', Or.inl (h.map (restrictEquiv (specialLinearInclusion J)))⟩
  · obtain ⟨e⟩ := h
    refine ⟨ι', Or.inr ⟨.mk e.toLinearEquiv ?_⟩⟩
    intro g
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro x
    have he := LinearMap.congr_fun (e.isIntertwining' (specialLinearInclusion J g)) v
    have hx := congrArg (fun f : Module.Dual K (Fin 3 → K) => f x) he
    simpa only [LinearMap.comp_apply, Representation.dual_apply, MonoidHom.comp_apply,
      map_inv, natural, word] using hx

end Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue
