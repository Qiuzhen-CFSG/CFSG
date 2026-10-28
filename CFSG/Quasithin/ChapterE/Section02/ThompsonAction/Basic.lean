module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import Theory.GroupTheory.ReducedNormal.Defs
public import Stellmacher.ElementaryAbelianMaxGlobal

/-!
# The original reduced-module preliminaries for E.2.3

Thompson movement forces J(H) outside the unique maximal-overgroup core,
so O²(H) lies in J(H). Reducedness makes the nontrivial centralizer quotient
minimal parabolic. Its kernel lies in that same core; intersecting with the
original Sylow gives C_T(U)=O₂(H). This constructs the normal Sylow subgroup
of the actual centralizer, without replacing that centralizer by a two-group.

Source: Aschbacher–Smith, B.6.8(6) and E.2.3(1), printed pp.114–115 and
216–217 (1 March 2004 manuscript).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G]

/-- The first containment in E.2.3 follows before any action classification. -/
theorem residual_le_thompson
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    pResidual 2 G ≤ elementaryAbelianMaxJ (⊤ : Subgroup G) ∧
      elementaryAbelianMaxJ (⊤ : Subgroup G) ⊔ (T : Subgroup G) = ⊤ := by
  let : (elementaryAbelianMaxJ (⊤ : Subgroup G)).Characteristic :=
    elementaryAbelianMaxJ_top_characteristic
  have hn : ¬ elementaryAbelianMaxJ (⊤ : Subgroup G) ≤
      ChapterB.minimalParabolicCore T hP := by
    intro h
    apply hJ
    apply le_trans ?_ (le_centralizer_iff.mp hU.le_centralizer_pCore)
    rw [← ChapterB.minimalParabolic_sylow_inf_core T hP]
    exact le_inf (sSup_le fun _ hA => hA.1)
      ((elementaryAbelianMaxJ_sylow_le_top T).trans h)
  exact ⟨(ChapterB.minimalParabolic_normal_subgroup_residual_dichotomy T hP _).resolve_left hn,
    (sup_comm _ _).trans
      ((ChapterB.minimalParabolic_normal_subgroup_dichotomy T hP _).resolve_left hn)⟩

/-- The centralizer has the original normal two-core as its actual Sylow subgroup. -/
theorem reduced_centralizer_sylow
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    let := hU.normal
    (T : Subgroup G) ⊓ centralizer (U : Set G) = pCore 2 G ∧
      ∃ S : Sylow 2 (centralizer (U : Set G)),
        (S : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
          pCore 2 G := by
  let := hU.normal
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hk : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [QuotientGroup.ker_mk'] at he
    change elementaryAbelianMaxJ (T : Subgroup G) ≤ C
    rw [he]
    exact le_top
  have hc : C ≤ ChapterB.minimalParabolicCore T hP := by
    have hh := (ChapterB.minimalParabolic_reduced_image T hP q
      (QuotientGroup.mk'_surjective C) hU.quotient_pCore_eq_bot hk).1
    simpa only [q, QuotientGroup.ker_mk'] using hh
  have hi : (T : Subgroup G) ⊓ C = pCore 2 G := by
    apply le_antisymm
    · exact (inf_le_inf_left _ hc).trans (ChapterB.minimalParabolic_sylow_inf_core T hP).le
    · exact le_inf (pCore_isPGroup.le_sylow_of_normal T)
        (le_centralizer_iff.mp hU.le_centralizer_pCore)
  refine ⟨hi, ?_⟩
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal C
  refine ⟨S, ?_⟩
  rw [hS]
  rw [← hi]
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨hc, c.property⟩
  · rintro ⟨ht, hc⟩
    exact ⟨⟨x, hc⟩, ht, rfl⟩

end CFSG.Quasithin.ChapterE.ThompsonAction
