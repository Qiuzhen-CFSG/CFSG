module
public import Theory.GroupTheory.UniqueMaximalSimplePair
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentAutomizer
/-!
# Unique Sylow overgroups in a pure component pair

A minimal parabolic whose component normalizer is precisely a commuting
product induces unique maximality on the intrinsic component Sylow. Every
proper component overgroup of that Sylow is invariant under its ambient
Sylow stabilizer, hence lies in the ambient unique maximal subgroup.

Source: Aschbacher--Smith B.6.8(3), applied to G.6.4(3), pp.114--115,346.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- Minimal parabolicity descends to a simple factor whose normalizer is its
commuting direct-product pair, with the original Sylow intersection retained. -/
theorem component_sylow_unique_of_pair_normalizer
    (T : Sylow 2 G) (hmin : IsMinimalParabolicOver T ⊤)
    (A B : Subgroup G) (hA : IsComponent G A) [IsSimpleGroup A]
    (heven : 2 ∣ Nat.card A) (hgen : A ⊔ (T : Subgroup G) = ⊤)
    (hc : A ≤ centralizer (B : Set G)) (hd : Disjoint A B)
    (hn : normalizer (A : Set G) = A ⊔ B) :
    Order.HasUniqueMaximalOver ((T : Subgroup G).subgroupOf A) ⊤ := by
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_subnormal A hA.1
  have hsplit := inf_sup_eq_sup_inf_of_disjoint_centralizing A B
    (T : Subgroup G) hc hd T.isPGroup' P hP
  let M := minimalParabolicMax T hmin
  have hTM : (T : Subgroup G) ≤ M := (minimalParabolicMax_spec T hmin).2
  have hAM : A ⊓ M < A := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have htop : (⊤ : Subgroup G) ≤ M := by
      rw [← hgen]
      exact sup_le (he ▸ inf_le_right) hTM
    exact (minimalParabolicMax_spec T hmin).1.ne_top (top_unique htop)
  have hbound (Q : Subgroup A) (hPQ : (T : Subgroup G).subgroupOf A ≤ Q)
      (hQ : Q < ⊤) : Q ≤ M.subgroupOf A := by
    let D := Q.map A.subtype
    have hDne : D ≠ ⊥ := by
      intro he
      have hQbot : Q = ⊥ := map_injective A.subtype_injective (he.trans (Subgroup.map_bot _).symm)
      exact component_sylow_intersection_ne_bot T hA heven (bot_unique (hPQ.trans_eq hQbot))
    have hDA : D ≠ A := by
      intro he
      apply hQ.ne
      apply map_injective A.subtype_injective
      simpa only [← MonoidHom.range_eq_map, range_subtype] using he
    have hinv : (T : Subgroup G) ⊓ normalizer (A : Set G) ≤ normalizer (D : Set G) := by
      rw [hn, inf_comm, hsplit]
      apply sup_le
      · apply le_trans _ D.le_normalizer
        intro a ha
        exact mem_map_of_mem A.subtype (hPQ (show (⟨a,ha.1⟩ : A) ∈ (T : Subgroup G).subgroupOf A from ha.2))
      · exact ((inf_le_left.trans (le_centralizer_iff.mp hc)).trans
          (centralizer_le (map_subtype_le Q))).trans (centralizer_le_normalizer _)
    have hDM := component_seed_le_minimalParabolicMax T hmin hA
      (map_subtype_le Q) hDne hDA hinv
    intro a ha
    exact hDM (mem_map_of_mem A.subtype ha)
  have hSM : (T : Subgroup G).subgroupOf A ≤ M.subgroupOf A :=
    subgroupOf_mono A hTM
  have hMlt : M.subgroupOf A < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    exact hAM.ne (inf_eq_left.mpr (subgroupOf_eq_top.mp he))
  have hcov : M.subgroupOf A ⋖ ⊤ :=
    ⟨hMlt, fun Q hMQ hQt => (not_lt_of_ge (hbound Q (hSM.trans hMQ.le) hQt)) hMQ⟩
  refine ⟨hSM.trans_lt hMlt, M.subgroupOf A, ⟨hSM,hcov⟩, ?_⟩
  intro Q hQ
  exact ((hQ.2.eq_or_eq (hbound Q hQ.1 hQ.2.lt) hMlt.le).resolve_right hMlt.ne).symm
end CFSG.Quasithin.ChapterB
