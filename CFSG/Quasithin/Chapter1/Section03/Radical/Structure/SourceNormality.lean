module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralNormality
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.LocalNormality
/-!
# Original local radical normality from the proved A.3.8 clause

Apply the unconditional normal-or-quasisimple result to the actual two-core
quotient of LT. The quotient component is not quasisimple, so it is normal;
the original subgroup and quotient correspondence then give T-invariance
and normality in LT. No ambient component classification is an input.

Source: Aschbacher--Smith A.3.8(3), p.46, and 13.1.4, p.867.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1
universe u
variable {G : Type u} [Group G] [Finite G]

theorem radicalLocal_invariant_source {κ : GroupClass.{u}}
    {T L₀ : Subgroup G} (hL : L₀ ∈ L G T)
    (hQ : IsSQTK κ ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) : T ≤ normalizer (L₀ : Set G) :=
  radicalLocal_invariant_of_A38
    (fun _ _ _ hG hO _ hC => ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hG hO hC)
    hL hQ hn

theorem radicalLocal_normal_source {κ : GroupClass.{u}}
    {T L₀ : Subgroup G} (hL : L₀ ∈ L G T)
    (hQ : IsSQTK κ ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) : (L₀.subgroupOf (L₀ ⊔ T)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (sup_le L₀.le_normalizer (radicalLocal_invariant_source hL hQ hn))

end CFSG.Quasithin.Chapter1
