module

public import Theory.Character.AlternatingSix.Golden
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InflatedCharacters

/-!
# Applying the complementary A₆ characters to the actual normalizer quotient

The golden-row deduction supplies the degree-eight input of the existing
inflation theorem, using its literal quotient map and its order-five marking.
The basis-completion and intrinsic conjugacy inputs are discharged by their
A₆ producers. Only the rational producer remains explicit in
`normalizerInflatedBlock_of_rational`; its assembly owner must supply it before
claiming the normalizer block from local analysis alone.

Source: Janko, *A characterization of the Mathieu simple groups, I* (1968),
§6, pp.10–11, characters χ₄ and χ₅.
-/

noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy Theory.Character.AlternatingSix

universe u
variable {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)

/-- Supply the golden rows through their complementary actual irreducibles.
The remaining inputs are precisely the rational producer and the two separate
construction obligations in `Golden.Interfaces`. -/
public theorem normalizerInflatedBlock_of_rational_and_completion
    (L : LocalAnalysisData D k) (Q : NormalizerClassData D k)
    (geometry : GoldenClassGeometry)
    (rational : ∀ c : alternatingGroup (Fin 6), orderOf c = 3 → Nonempty (RationalBlock c))
    (completion : ∀ c : alternatingGroup (Fin 6), orderOf c = 3 →
      ∀ R : RationalBlock c, Nonempty (RationalCompletion R)) :
    Nonempty (NormalizerInflatedBlock Q) := by
  apply normalizerInflatedBlock_of_alternatingSix_blocks D k L Q rational
  intro c μ hc hμ R
  obtain ⟨C⟩ := completion c hc R
  exact goldenBlock_of_completion R C geometry hμ

/-- Supply the two golden characters on the literal normalizer quotient.
Only the independent rational-character producer remains to be supplied by
the final normalizer assembly. -/
public theorem normalizerInflatedBlock_of_rational
    (L : LocalAnalysisData D k) (Q : NormalizerClassData D k)
    (rational : ∀ c : alternatingGroup (Fin 6), orderOf c = 3 → Nonempty (RationalBlock c)) :
    Nonempty (NormalizerInflatedBlock Q) :=
  normalizerInflatedBlock_of_alternatingSix_blocks D k L Q rational goldenBlock_of_rational

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
