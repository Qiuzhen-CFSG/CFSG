module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionLocalTable
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionGraphSylowModel
public import Theory.SpecificGroups.SymmetricFourWreath.LargeCentralizer

/-!
# Source fusion from the large-centralizer classes of the Sylow

The marked source Sylow has the dihedral wreath model. Its root generates
its center, and the literal short involution has centralizer order 64.
The wreath calculation therefore places every involution with centralizer
larger than 32 in the root or short class. All conjugacies here already
occur in the source Sylow subgroup.

The exceptional enlargement of the graph centralizer, whose original
Sylow-centralizer has order 32, now forces graph/short fusion. The existing
ambient Sylow argument then proves that the literal `C_T(t)` is Sylow in
`C_G(t)`. This discharges the three local fusion inputs used by the F.5.4
normalizer calculation without assuming the other fields of `FusionFacts`.

Source: Aschbacher--Smith F.4.37 and F.5.3--4, printed pp.293, 300--301.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open BinaryPermutation.AlternatingFiveExtension
local notation "hn" => Nat.le_refl 1

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

private def sourceTCentralizerEquiv (x : Source.sylowImage c i) :
    centralizer ({x} : Set (Source.sylowImage c i)) ≃* Tcentralizer c i x.val where
  toFun a := ⟨a.val.val,a.val.property,
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_centralizer_singleton_iff.mp a.property))⟩
  invFun a := ⟨⟨a.val,a.property.1⟩,mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp a.property.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable [Finite G]

/-- Every source Sylow involution with centralizer larger than 32 is root or short. -/
theorem source_large_centralizer_classes_in_T (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (x : G) (hx : x ∈ Source.sylowImage c i)
    (ho : orderOf x = 2) :
    IsConj (rootElement c i z) x ∨
      (∃ y ∈ Source.sylowImage c i, y * sourceMarkedShort c i * y⁻¹ = x) ∨
      Nat.card (Tcentralizer c i x) ≤ 32 := by
  classical
  let T := Source.sylowImage c i
  let xT : T := ⟨x,hx⟩
  let tT : T := ⟨sourceMarkedShort c i,source_short_mem_sylowImage c i⟩
  obtain ⟨e,he⟩ := exists_source_marked_sylow_equiv c i h.embedding_injective
  have hto : orderOf tT = 2 :=
    (orderOf_injective T.subtype T.subtype_injective tT).symm.trans
      (source_short_order c i h.embedding_injective)
  have hxo : orderOf xT = 2 := (orderOf_injective T.subtype T.subtype_injective xT).symm.trans ho
  have htcard : Nat.card (centralizer ({tT} : Set T)) = 64 :=
    (Nat.card_congr (sourceTCentralizerEquiv c i tT).toEquiv).trans
      (source_short_Tcentralizer_card c i h.embedding_injective)
  obtain hz | hconj | hsmall := SymmetricFourWreath.LargeCentralizer.large_centralizer_cases_of_equiv
    (e.trans SylowModel.wreathEquiv) tT xT hto htcard hxo
  · left
    have hxin : x ∈ zpowers (rootElement c i z) := by
      rw [←pointRootImage_eq_zpowers c i z h,
        ←source_sylowImage_center_eq_pointRoot c i z h]
      exact mem_map_of_mem T.subtype hz
    rw [mem_zpowers_iff_mem_range_orderOf,source_root_order c i z h] at hxin
    obtain ⟨n,hnmem,he⟩ := Finset.mem_image.mp hxin
    have hn2 := Finset.mem_range.mp hnmem
    interval_cases n
    · have hxone : x = 1 := by simpa using he.symm
      rw [hxone,orderOf_one] at ho
      omega
    · have hxeq : rootElement c i z = x := by simpa using he
      exact hxeq ▸ IsConj.refl (rootElement c i z)
  · obtain ⟨y,hy⟩ := isConj_iff.mp hconj
    exact Or.inr (Or.inl ⟨y.val,y.property,congrArg Subtype.val hy⟩)
  · right; right
    exact (Nat.card_congr (sourceTCentralizerEquiv c i xT).symm.toEquiv).le.trans hsmall

/-- The forgetful ambient-conjugacy version of the controlled Sylow table. -/
theorem source_large_centralizer_classes (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (x : G) (hx : x ∈ Source.sylowImage c i)
    (ho : orderOf x = 2) :
    IsConj (rootElement c i z) x ∨ IsConj (sourceMarkedShort c i) x ∨
      Nat.card (Tcentralizer c i x) ≤ 32 := by
  obtain hz | ⟨y,hy,he⟩ | hs := source_large_centralizer_classes_in_T c i z h x hx ho
  · exact Or.inl hz
  · exact Or.inr (Or.inl (isConj_iff.mpr ⟨y,he⟩))
  · exact Or.inr (Or.inr hs)

/-- The exceptional source graph involution is fused to the literal short root. -/
theorem source_graph_fuses_short (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (hex : Source.Exceptional c i) :
    IsConj (Source.graphElement c i) (sourceMarkedShort c i) :=
  source_graph_fuses_short_of_local_table c i z h hex
    (source_Tf_card c i h.embedding_injective) (source_large_centralizer_classes c i z h)

/-- The literal C_T(t) is Sylow in the ambient short-root centralizer. -/
theorem source_short_centralizer_sylow (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (hex : Source.Exceptional c i) :
    ∃ R : Sylow 2 (centralizer ({sourceMarkedShort c i} : Set G)),
      (R : Subgroup (centralizer ({sourceMarkedShort c i} : Set G))) =
        (Source.sylowImage c i).subgroupOf (centralizer ({sourceMarkedShort c i} : Set G)) :=
  (source_short_fusion_and_sylow_of_local_table c i z h hex
    (source_Tf_card c i h.embedding_injective) (source_large_centralizer_classes c i z h)
    (source_short_Tcentralizer_iso c i h.embedding_injective)).2

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
