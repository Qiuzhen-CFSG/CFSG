module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionPlaneCommutator
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerPlane
/-!
# Source roots in both endpoint graph cores

The plane radical is normalized by the literal plane endpoint. Its intersection
with the graph centralizer is therefore a normal two-subgroup of E₂ and lies
in A₂. The previously proved plane-root marking puts the original source root
in that intersection. The graph involution also lies in each Aᵢ. Together with
the original root-centralizer equality, these memberships place C_G(Aᵢ) inside
E₁, supplying the geometric reduction in the F.5.4 self-centralizer argument.

Source: Aschbacher–Smith, F.5.3(1) and F.5.4(1), printed pp.300–301.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

omit [Finite G] in
theorem source_Q_plane_inf_C_le_A (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    Q c i true ⊓ C c i ≤ A c i true := by
  have hQ : Q c i true ≤ M c i true := by
    rw [← normalizer_Q_eq_plane c i z h]
    exact (Q c i true).le_normalizer
  have hnorm : E c i true ≤ normalizer (Q c i true ⊓ C c i : Set G) := by
    apply le_trans _ inf_normalizer_le_normalizer_inf
    exact le_inf (by rw [normalizer_Q_eq_plane c i z h]; exact inf_le_left)
      (inf_le_right.trans (C c i).le_normalizer)
  have hp : IsPGroup 2 (Q c i true) := by
    let := source_Q_plane_elementary c i
    exact IsElementaryAbelian.isPGroup 2 _
  exact le_pCoreIn_of_normalizes (hp.to_inf_left) (inf_le_inf hQ le_rfl) hnorm

theorem source_root_mem_A_plane (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) :
    rootElement c i z ∈ A c i true :=
  source_Q_plane_inf_C_le_A c i z h ⟨source_root_mem_Q_plane c i z h,
    mem_centralizer_singleton_iff.mpr (source_graph_commutes_root c i z h).symm.eq⟩

theorem source_root_mem_A (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z) (b : Bool) :
    rootElement c i z ∈ A c i b := by
  cases b
  · exact source_root_mem_A_point c i z h
  · exact source_root_mem_A_plane c i z h

theorem source_graph_mem_A (hi : Function.Injective i) (b : Bool) :
    Source.graphElement c i ∈ A c i b := by
  have ho := source_graph_order c i hi
  have hp : IsPGroup 2 (zpowers (Source.graphElement c i)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,ho]; rfl)
  have hnorm : E c i b ≤ normalizer (zpowers (Source.graphElement c i) : Set G) := by
    rw [normalizer_zpowers_eq_centralizer_of_order_two _ ho]
    exact inf_le_right
  exact le_pCoreIn_of_normalizes hp (zpowers_le.mpr (graph_mem_E c i b)) hnorm (mem_zpowers _)

/-- The source roots put each endpoint core's ambient centralizer into E1. -/
theorem source_centralizer_A_le_E_point (z : pointParabolic 1 hn)
    (h : Source.Hypotheses c i z) (b : Bool) :
    centralizer (A c i b : Set G) ≤ E c i false := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [← source_root_centralizer c i z h]
    exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hx _ (source_root_mem_A c i z h b)).symm
  · exact mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hx _ (source_graph_mem_A c i h.embedding_injective b)).symm
end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
