module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralNormality
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The complete nonnormal C-component source in 1.2.1(3)

A nonnormal C-component stays nonnormal in the actual quotient by O₂(G).
The normal-or-quasisimple theorem makes this quotient image an ordinary
component. The existing four-model source therefore applies to that image,
and the canonical intrinsic two-core quotient isomorphism returns its actual
model to B/O₂(B). Solvable-quotient transport preserves the normalizer index.

No ordinary-component hypothesis is imposed on the original B. The general
source theorem retains exactly the earlier universal A/C inputs; the final
known-simple theorem instantiates their completed source proofs.

Source: Aschbacher--Smith A.3.8(3), pp.45--46, and 1.2.1(3), p.504.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The actual image of a nonnormal C-component modulo the ambient two-core
is an ordinary component, even when the original subgroup is not quasisimple. -/
theorem nonnormal_twoCore_image_isComponent
    (hQ : IsSQTK κ (G ⧸ pCore 2 G))
    {B : Subgroup G} (hB : B.IsCComponent) (hn : ¬ B.Normal) :
    IsComponent (G ⧸ pCore 2 G) (B.map (QuotientGroup.mk' (pCore 2 G))) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  have hbar := hB.map_quotient (pCore 2 G)
  have hnon : ¬ (B.map (QuotientGroup.mk' (pCore 2 G))).Normal :=
    fun hh => hn (cComponent_normal_of_quotient_normal hB (pCore 2 G) hh)
  exact ⟨hbar.subnormal,
    (ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hQ
      (pCore_quotient_pCore_eq_bot 2) hbar).resolve_left hnon⟩

/-- Full 1.2.1(3) for general C-components, with only the genuine earlier A/C
source inputs and the original SQTK hypothesis on the two-core quotient. -/
theorem proposition_1_2_1_three_index_source
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    {B : Subgroup G} (hB : B.IsCComponent) :
    B.Normal ∨ (normalizer (B : Set G)).index = 2 ∧
      NonnormalCComponentModel (B ⧸ pCore 2 B) := by
  classical
  by_cases hn : B.Normal
  · exact Or.inl hn
  let := pCore_isNilpotent (p := 2) (G := G)
  have hnon : ¬ (B.map (QuotientGroup.mk' (pCore 2 G))).Normal :=
    fun hh => hn (cComponent_normal_of_quotient_normal hB (pCore 2 G) hh)
  obtain ⟨hi,hm⟩ :=
    ChapterA.SQTKStructure.NonnormalOuterSource.nonnormal_component_index_and_model
      hA hC hQ (pCore_quotient_pCore_eq_bot 2) _
      (nonnormal_twoCore_image_isComponent hQ hB hn) hnon
  exact Or.inr ⟨(cComponent_normalizer_index_quotient hB (pCore 2 G)).symm.trans hi,
    hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hB)⟩

/-- The actual known-simple catalogue discharges both earlier source inputs. -/
theorem proposition_1_2_1_three_index_knownSimple
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    {B : Subgroup G} (hB : B.IsCComponent) :
    B.Normal ∨ (normalizer (B : Set G)).index = 2 ∧
      NonnormalCComponentModel (B ⧸ pCore 2 B) :=
  proposition_1_2_1_three_index_source
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hQ hB

/-- The original conjugacy-family cardinality formulation of 1.2.1(3). -/
theorem proposition_1_2_1_three_knownSimple
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    {B : Subgroup G} (hB : B.IsCComponent) :
    B.Normal ∨ (Set.range fun g : G => B.map (MulAut.conj g).toMonoidHom).ncard = 2 ∧
      NonnormalCComponentModel (B ⧸ pCore 2 B) := by
  rw [ncard_conjugates_eq_index_normalizer]
  exact proposition_1_2_1_three_index_knownSimple hQ hB

end CFSG.Quasithin.Chapter1.Section02
