module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOrdinary
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.SourceNormality
/-!
# Full nonnormal C-component models and radical invariance

The pre-ordinary A.3.8 step supplies quasisimplicity for the actual C-component.
The checked ordinary four-model theorem now gives the source catalogue and
normalizer index without an ordinary-component premise. The same universal
normal-or-quasisimple theorem discharges the earlier input in the original
radical-family invariance application, keeping its literal two-core quotient.
The individual radical-invariance theorem is re-exported from its Chapter 1
owner, so the two source branches share the same public declaration.

Source: Aschbacher–Smith A.3.8(3), printed pp.45–46, and 1.3.3, p.509.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.NonnormalOrdinary

/-- The full A.3.8(3) alternative on the original known-simple C-component. -/
theorem index_and_model_knownSimple {G:Type*} [Group G] [Finite G]
    (hG:IsSQTK KnownSimple.IsKnownSimple G) (hO:pCore 2 G=⊥)
    (B:Subgroup G) (hB:B.IsCComponent) :
    B.Normal ∨ (normalizer (B:Set G)).index=2 ∧
      Chapter1.Section02.NonnormalCComponentModel B := by
  by_cases hn:B.Normal
  · exact Or.inl hn
  · have hordinary:IsComponent G B:=⟨hB.subnormal,quasisimple_of_not_normal hG hO B hB hn⟩
    exact Or.inr (ChapterA.SQTKStructure.NonnormalOuterSource.nonnormal_component_index_and_model
      (fun _ _ _=>ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _=>ChapterA.Section02.theoremC_knownSimple) hG hO B hordinary hn)
end CFSG.Quasithin.ChapterA.Section03.NonnormalOrdinary

namespace CFSG.Quasithin.Chapter1
variable {G:Type*} [Group G] [Finite G] {κ:GroupClass}
/-- Every actual radical-family member is invariant under its original actor. -/
theorem XiRad_invariant_source {T:Subgroup G}
    (hQ:∀L₀∈L G T,IsSQTK κ ((L₀⊔T:Subgroup G)⧸pCore 2 (L₀⊔T:Subgroup G)))
    {X:Subgroup G} (hX:X∈XiRad G T) : T≤normalizer (X:Set G) :=
  XiRad_invariant_of_A38
    (fun _ _ _ hE hO C hC=>ChapterA.Section03.NonnormalOrdinary.normal_or_quasisimple hE hO C hC)
    hQ hX
end CFSG.Quasithin.Chapter1
