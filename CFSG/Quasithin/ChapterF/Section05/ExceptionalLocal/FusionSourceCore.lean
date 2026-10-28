module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionLocalTableLarge
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionGraphCenter
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionPlaneClasses
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionSubgroup

/-!
# Source-complete exceptional fusion interfaces

The original F.5 hypotheses imply exceptionality by transfer. The literal
Sylow and centralizer models then give graph–short fusion, the ambient Sylow
property of the short centralizer, and the root-product fusions. The plane
root class has five elements.

The final two theorems retain conjugators in `i.range ∨ N_G(A₂)`, the exact
subgroup used in the F.5.6 generation argument. The only additional input
there is the chosen graph-centralizer Sylow subgroup lying in `N_G(A₂)`;
its proof belongs to the subsequent normalizer analysis.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, F.4.37–38
and F.5.3–6, printed pp.293–294 and 300–304.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

theorem source_short_fusion_of_hypotheses (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) :
    IsConj (Source.graphElement c i) (sourceMarkedShort c i) :=
  source_graph_fuses_short c i z h (source_exceptional c i z h)

theorem source_short_sylow_of_hypotheses (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) :
    ∃ R : Sylow 2 (centralizer ({sourceMarkedShort c i} : Set G)),
      (R : Subgroup (centralizer ({sourceMarkedShort c i} : Set G))) =
        (Source.sylowImage c i).subgroupOf
          (centralizer ({sourceMarkedShort c i} : Set G)) :=
  source_short_centralizer_sylow c i z h (source_exceptional c i z h)

theorem source_root_product_conjugator (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i))) :
    ∃ g ∈ Rimage c i R ⊔ Q c i true,
      g * rootElement c i z * g⁻¹ = Source.graphElement c i * rootElement c i z := by
  have hstrict : Tf c i < (R : Subgroup (C c i)) := lt_of_le_of_ne hR (by
    intro he
    exact source_exceptional c i z h ⟨R,he.symm⟩)
  exact source_root_fusion_from_graph_fusion c i z h
    (source_Tf_sylow_point c i h.embedding_injective) R hstrict
    (source_short_fusion_of_hypotheses c i z h)

theorem source_root_product_fusion (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) :
    IsConj (rootElement c i z) (Source.graphElement c i * rootElement c i z) := by
  obtain ⟨R,hR⟩ := exists_strict_sylow c i (source_sylowImage_isTwoGroup c i)
    (source_exceptional c i z h)
  obtain ⟨g,_,hg⟩ := source_root_product_conjugator c i z h R hR.le
  exact isConj_iff.mpr ⟨g,hg⟩

theorem source_root_short_product_fusion (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) :
    IsConj (rootElement c i z)
      (Source.graphElement c i * sourceMarkedShort c i * rootElement c i z) :=
  source_root_fuses_graph_short_root_of_graph_root c i z h
    (source_root_product_fusion c i z h)

theorem source_root_class_Q_plane (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) :
    Nat.card (classIntersection (rootElement c i z) (Q c i true)) = 5 :=
  source_root_class_Q_plane_of_graph_fusion c i z h
    (source_short_fusion_of_hypotheses c i z h)

/-- Both required fusions retain their witnesses in the exact final join. -/
theorem source_controlled_graph_short_fusion (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (hRH : Rimage c i R ≤ H c i) :
    ∃ g ∈ i.range ⊔ H c i,
      g * Source.graphElement c i * g⁻¹ = sourceMarkedShort c i :=
  source_graph_short_conjugator_in_join c i z h R hR hRH
    (source_large_centralizer_classes_in_T c i z h)

theorem source_controlled_root_product_fusion (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z)
    (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
    (hRH : Rimage c i R ≤ H c i) :
    ∃ g ∈ i.range ⊔ H c i,
      g * rootElement c i z * g⁻¹ = Source.graphElement c i * rootElement c i z := by
  obtain ⟨g,hg,he⟩ := source_root_product_conjugator c i z h R hR
  refine ⟨g,?_,he⟩
  apply (show Rimage c i R ⊔ Q c i true ≤ i.range ⊔ H c i from
    sup_le (hRH.trans le_sup_right)
      ((source_Q_plane_le_sylowImage c i).trans
        (((sylowImage_le_M c i false).trans (M_le_completion c i false)).trans le_sup_left)))
  exact hg

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
