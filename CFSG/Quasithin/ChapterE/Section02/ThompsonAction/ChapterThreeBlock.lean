module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SourceConclusions
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ComponentBlockSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ChapterThreeSylow
/-!
# The block exit on the original Chapter 3 omega orbit

The existing qrc source supplies SQTK, characteristic two, minimal
parabolicity, reducedness and Thompson movement for the actual omega-center
orbit in H. The complete block source now applies to that original group
and intrinsic Sylow, with only the literal characteristic-Baumann antecedent.
The already complete residual-Sylow source is imported at the same boundary.

Source: Aschbacher–Smith E.2.3(4), 3.1.7, pp.217,575–576.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

theorem QrcHypotheses.e23_chiZero_block_source
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype)
    (hno : let S := T.subtype h.right_mem.1.1.2
      ∀ D : Subgroup (ChapterB.baumann (S : Subgroup H)), D.Characteristic →
        (D.map (ChapterB.baumann (S : Subgroup H)).subtype).Normal → D = ⊥) :
    let S := T.subtype h.right_mem.1.1.2
    ∃ L : Subgroup H, ChapterC.IsChiZeroBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (S : Subgroup H)⁆ ∧ L ⊔ (S : Subgroup H) = ⊤ := by
  obtain ⟨hsq,hf,hp,hU,hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  obtain ⟨L,hL,hm,hgen,_⟩ := ChapterE.ThompsonAction.source_chiZero_block
    hsq _ hp hf _ hU hj hno
  exact ⟨L,hL,hm,hgen⟩

theorem QrcHypotheses.e23_nonsolvable_block_source
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hs : ¬Group.IsSolvable H) (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype)
    (hno : let S := T.subtype h.right_mem.1.1.2
      ∀ D : Subgroup (ChapterB.baumann (S : Subgroup H)), D.Characteristic →
        (D.map (ChapterB.baumann (S : Subgroup H)).subtype).Normal → D = ⊥) :
    let S := T.subtype h.right_mem.1.1.2
    ∃ L : Subgroup H, ChapterC.IsBlock L ∧
      ((∃ n, ChapterC.IsL2EvenBlock L n) ∨ ChapterC.IsAlternatingBlock L 5) ∧
      L = ⁅L,elementaryAbelianMaxJ (S : Subgroup H)⁆ ∧ L ⊔ (S : Subgroup H) = ⊤ := by
  obtain ⟨hsq,hf,hp,hU,hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  obtain ⟨L,hL,ht,hm,hgen,_⟩ := ChapterE.ThompsonAction.source_nonsolvable_block
    hsq _ hp hf hs _ hU hj hno
  exact ⟨L,hL,ht,hm,hgen⟩
theorem QrcHypotheses.e23_nonsolvable_component_block_source
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hs : ¬Group.IsSolvable H) (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype)
    (hno : let S := T.subtype h.right_mem.1.1.2
      ∀ D : Subgroup (ChapterB.baumann (S : Subgroup H)), D.Characteristic →
        (D.map (ChapterB.baumann (S : Subgroup H)).subtype).Normal → D = ⊥) :
    let S := T.subtype h.right_mem.1.1.2
    ∃ L : Subgroup H, L.IsCComponent ∧ ChapterC.IsBlock L ∧
      ((∃ n, ChapterC.IsL2EvenBlock L n) ∨ ChapterC.IsAlternatingBlock L 5) ∧
      L = ⁅L,elementaryAbelianMaxJ (S : Subgroup H)⁆ ∧ L ⊔ (S : Subgroup H) = ⊤ := by
  obtain ⟨hsq,hf,hp,hU,hj⟩ := h.e23_hypotheses hG hM hu hJ hZ
  obtain ⟨L,hc,hL,ht,hm,hgen,_⟩ := ChapterE.ThompsonAction.source_nonsolvable_component_block
    hsq _ hp hf hs _ hU hj hno
  exact ⟨L,hc,hL,ht,hm,hgen⟩
end CFSG.Quasithin.Chapter3
