module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels.Coordinates
public import Theory.Representation.HexacodeAction.NormalOvergroup

/-!
# The full covered-six moved-action embedding

Extend the constructed component coordinates to the original actor through
the exact binary normalizer. The result includes every even hexacode element
in its image and intertwines the full original moved action. These are the
precise action and even-range inputs of the source normalizer contradiction.

Source: Aschbacher--Smith K.1.3 and 13.6.22, printed pp.453 and 932.
-/

public section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels
universe u w
variable {D : Type u} [Group D]
  {V : Type w} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {C : Subgroup D} [C.Normal]

/-- Full source coordinates include the original component marking and the
entire even-cover range, without assuming an exceptional-block predicate. -/
theorem ActionData.exists_full_model (m : ActionData ρ C)
    (eC : C ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hquot : IsPGroup 2 (D ⧸ C)) (hcore : pCore 2 D = ⊥) :
    ∃ (f : D →* Atlas.Codes.HexAutomorphisms)
      (c : C ≃* Atlas.Codes.HexEvenAutomorphisms)
      (e : m.ambientSection.space.toSubmodule ≃ₗ[ZMod 2] Atlas.Codes.hexacode),
      Function.Injective f ∧ Atlas.Codes.hexSign.ker ≤ f.range ∧
      (∀ g : C, f g = (c g).val) ∧
      ∀ (g : D) (v : m.ambientSection.space.toSubmodule),
        e (m.ambientSection.space.toRepresentation g v) = Hexacode.action (f g) (e v) := by
  obtain ⟨a⟩ := m.ambient_hexacode_coordinates eC
  obtain ⟨f, hf, hc, he⟩ := Hexacode.exists_full_embedding
    m.ambientSection.space.toRepresentation C hquot hcore
    a.groupEquiv a.linearEquiv a.intertwines
  refine ⟨f, a.groupEquiv, a.linearEquiv, hf, ?_, hc, he⟩
  intro g hg
  obtain ⟨c, hcg⟩ := a.groupEquiv.surjective ⟨g, hg⟩
  exact ⟨c, (hc c).trans (congrArg Subtype.val hcg)⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels
